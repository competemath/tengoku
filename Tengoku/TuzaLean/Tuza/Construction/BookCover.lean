import Tengoku.TuzaLean.Tuza.Construction.Setup
import Tengoku.TuzaLean.Tuza.Books.Layered
import Tengoku.TuzaLean.Tuza.Books.Cover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The three-page book cover: equation (5). -/

namespace Tuza

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)}

/-- The maximum residual packing Q and its maximum blue-edge residual packing Q1.-/
structure RefinedConstruction (c : Construction edges) where
  second : Finset (Finset (Sym2 V))
  second_maximum : IsMaximumPacking c.specialFamily second
  third : Finset (Finset (Sym2 V))
  third_maximum : IsMaximumPacking
    (residual c.specialFamily (blueEdges c.newEdges second)) third

/--
@isnad1 id=nonempty.0h3v.s4.0ca40959406e from=translated src=- shape=6341e258 vocab=54bb2b23
-/
theorem exists_refinedConstruction (c : Construction edges) :
    Nonempty (RefinedConstruction c) := by
  obtain ⟨Q, hQ⟩ := exists_maximumPacking c.specialFamily
  obtain ⟨Q1, hQ1⟩ := exists_maximumPacking
    (residual c.specialFamily (blueEdges c.newEdges Q))
  exact ⟨⟨Q, hQ, Q1, hQ1⟩⟩

namespace ThreeLayer

variable {c : Construction edges} (r : RefinedConstruction c)

/--
@isnad1 id=ispackin.0h4v.s5.4f0a52d09e1f from=translated src=- shape=d7d9a4ca vocab=67a30204
-/
theorem second_packing : IsPacking c.specialFamily r.second := r.second_maximum.1

/--
@isnad1 id=ispackin.0h4v.s5.9d448493abb5 from=translated src=- shape=d7d9a4ca vocab=a5595b90
-/
theorem third_packing : IsPacking c.specialFamily r.third :=
  r.third_maximum.1.mono_family (filter_subset _ _)

def pages (p : {T // T ∈ c.rest}) : Finset (Finset (Sym2 V)) :=
  Layered.twoLayerPages c.newEdges c.rest (r.second ∪ r.third) p

/--
@isnad1 id=iff.0h6v.s8.618034168ccf from=translated src=- shape=2e5749fe vocab=4712b46b
-/
@[simp] theorem mem_pages {p : {T // T ∈ c.rest}} {T : Finset (Sym2 V)} :
    T ∈ pages r p ↔ T = p.val ∨
      (T ∈ r.second ∪ r.third ∧ T ∩ c.newEdges = p.val ∩ c.newEdges) :=
  Layered.mem_twoLayerPages

/--
@isnad1 id=mem.0h5v.s6.e0227362c1f4 from=translated src=- shape=deb52cfa vocab=32ecd5d0
-/
theorem parent_mem_pages (p : {T // T ∈ c.rest}) : p.val ∈ pages r p :=
  (mem_pages r).mpr (Or.inl rfl)

/--
@isnad1 id=mem.1h5v.s6.e91ec28c6c63 from=translated src=- shape=7b8b8646 vocab=a4e5bc2e
-/
theorem child_actual {T : Finset (Sym2 V)} (hT : T ∈ r.second ∪ r.third) :
    T ∈ c.specialFamily := by
  rcases mem_union.mp hT with hT | hT
  · exact r.second_maximum.1.1 hT
  · exact (third_packing r).1 hT

/--
@isnad1 id=le.0h4v.s6.e398ba521aae from=translated src=- shape=b907be2f vocab=8aa99d69
-/
theorem rest_red_card_le_one (p : {T // T ∈ c.rest}) :
    (p.val ∩ c.newEdges).card ≤ 1 := by
  apply le_trans (card_le_card ?_) (c.remaining_new_le_one (c.rest_packing.1 p.property))
  intro e he
  exact mem_sdiff.mpr ⟨(mem_inter.mp he).1, (mem_sdiff.mp (mem_inter.mp he).2).2⟩

/--
@isnad1 id=eq.2h5v.s7.b5be6a8ba957 from=translated src=- shape=da86fc48 vocab=58d0ccf3
-/
theorem rest_red_eq_singleton (p : {T // T ∈ c.rest}) {e : Sym2 V}
    (hep : e ∈ p.val) (heN : e ∈ c.newEdges) : p.val ∩ c.newEdges = {e} := by
  ext f
  constructor
  · intro hf
    exact mem_singleton.mpr
      (card_le_one.mp (rest_red_card_le_one (c := c) p) f hf e (mem_inter.mpr ⟨hep, heN⟩))
  · intro hf
    rw [mem_singleton.mp hf]
    exact mem_inter.mpr ⟨hep, heN⟩

/--
@isnad1 id=eq.3h6v.s8.d3c1af358fe8 from=translated src=- shape=91d4de6c vocab=c3354b07
-/
theorem owner_unique {T : Finset (Sym2 V)} (hT : T ∈ c.specialFamily)
    (p p' : {T // T ∈ c.rest})
    (hp : T ∩ c.newEdges = p.val ∩ c.newEdges)
    (hp' : T ∩ c.newEdges = p'.val ∩ c.newEdges) : p = p' := by
  by_contra hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  have hn : (T ∩ c.newEdges).Nonempty :=
    card_pos.mp (by rw [(c.specialFamily_colored T hT).2]; decide)
  obtain ⟨e, he⟩ := hn
  exact disjoint_left.mp (c.rest_packing.2 p.property p'.property hval)
    (mem_inter.mp (hp ▸ he)).1 (mem_inter.mp (hp' ▸ he)).1

/--
@isnad1 id=ex.1h4v.s7.88f0ddbe808b from=translated src=- shape=b9223c74 vocab=c3354b07
-/
theorem exists_parent {T : Finset (Sym2 V)} (hT : T ∈ c.specialFamily) :
    ∃ p : {T // T ∈ c.rest}, T ∩ c.newEdges = p.val ∩ c.newEdges := by
  have hn : (T ∩ c.newEdges).Nonempty :=
    card_pos.mp (by rw [(c.specialFamily_colored T hT).2]; decide)
  obtain ⟨e, heT, heN⟩ := show ∃ e, e ∈ T ∧ e ∈ c.newEdges from by
    obtain ⟨e, he⟩ := hn
    exact ⟨e, (mem_inter.mp he).1, (mem_inter.mp he).2⟩
  obtain ⟨p, hp, hep⟩ := mem_support.mp (mem_sdiff.mp heN).1
  refine ⟨⟨p, hp⟩, ?_⟩
  exact (c.specialFamily_colored.red_eq_singleton hT heT heN).trans
    (rest_red_eq_singleton (c := c) ⟨p, hp⟩ hep heN).symm

/--
@isnad1 id=eq.1h4v.s6.860c8ffb1604 from=translated src=- shape=56bb8cab vocab=2e8b5e14
-/
theorem special_inter_rest {T : Finset (Sym2 V)} (hT : T ∈ c.specialFamily) :
    T ∩ support c.rest = T ∩ c.newEdges := by
  have hd := (mem_residual.mp (c.specialFamily_eq_residual ▸ hT)).2
  ext e
  constructor
  · intro he
    obtain ⟨heT, heP⟩ := mem_inter.mp he
    refine mem_inter.mpr ⟨heT, mem_sdiff.mpr ⟨heP, ?_⟩⟩
    intro heO
    exact disjoint_left.mp hd heT (mem_inter.mpr ⟨heP, heO⟩)
  · intro he
    exact mem_inter.mpr ⟨(mem_inter.mp he).1, (mem_sdiff.mp (mem_inter.mp he).2).1⟩

/--
@isnad1 id=not.1h4v.s6.9917e36d42bd from=translated src=- shape=4588a6ad vocab=938797bd
-/
theorem special_not_rest {T : Finset (Sym2 V)} (hT : T ∈ c.specialFamily) :
    T ∉ c.rest := by
  intro hp
  have heq : T ∩ support c.rest = T := inter_eq_left.mpr
    (fun _ he => mem_support.mpr ⟨T, hp, he⟩)
  have hc := congrArg Finset.card (special_inter_rest (c := c) hT)
  rw [heq, (c.specialFamily_colored T hT).1, (c.specialFamily_colored T hT).2] at hc
  omega

/--
@isnad1 id=le.1h5v.s6.c00f1523bae1 from=translated src=- shape=c4cd237a vocab=38fa416e
-/
theorem children_card_le_one {K : Finset (Finset (Sym2 V))}
    (hK : IsPacking c.specialFamily K) (p : Finset (Sym2 V)) :
    (Layered.children c.newEdges K p).card ≤ 1 := by
  apply card_le_one.mpr
  intro T hT U hU
  obtain ⟨hTK, hTp⟩ := Layered.mem_children.mp hT
  obtain ⟨hUK, hUp⟩ := Layered.mem_children.mp hU
  exact hK.red_inter_injective c.specialFamily_colored hTK hUK (hTp.trans hUp.symm)

/--
@isnad1 id=disjoint.0h4v.s5.1437255ced3f from=translated src=- shape=072b999f vocab=fcec2b85
-/
theorem second_third_disjoint : Disjoint r.second r.third := by
  apply disjoint_left.mpr
  intro T hTQ hTQ1
  exact Layered.residual_member_not_parent c.specialFamily_colored
    r.third_maximum.1 hTQ1 hTQ

/--
@isnad1 id=eq.0h5v.s7.4b787da2656e from=translated src=- shape=d7984279 vocab=c7854770
-/
theorem children_union (p : Finset (Sym2 V)) :
    Layered.children c.newEdges (r.second ∪ r.third) p =
      Layered.children c.newEdges r.second p ∪ Layered.children c.newEdges r.third p := by
  simp [Layered.children, filter_union]

/--
@isnad1 id=not.0h5v.s7.7125183dc27d from=translated src=- shape=9b9c9ff0 vocab=923da5ae
-/
theorem parent_not_child (p : {T // T ∈ c.rest}) :
    p.val ∉ Layered.children c.newEdges (r.second ∪ r.third) p.val := by
  intro hp
  exact special_not_rest (child_actual r (Layered.mem_children.mp hp).1) p.property

/--
@isnad1 id=nonempty.0h5v.s6.08e98f779c6f from=translated src=- shape=a62032d0 vocab=503478dc
-/
theorem pages_nonempty (p : {T // T ∈ c.rest}) : (pages r p).Nonempty :=
  ⟨p.val, parent_mem_pages r p⟩

/--
@isnad1 id=le.0h5v.s6.4efaa0ce06cd from=translated src=- shape=8cf1a13c vocab=adc6b225
-/
theorem pages_card_le_three (p : {T // T ∈ c.rest}) : (pages r p).card ≤ 3 := by
  have hq := children_card_le_one (second_packing r) p.val
  have hq1 := children_card_le_one (third_packing r) p.val
  have hu := card_union_le (Layered.children c.newEdges r.second p.val)
    (Layered.children c.newEdges r.third p.val)
  change (insert p.val (Layered.children c.newEdges (r.second ∪ r.third) p.val)).card ≤ 3
  rw [card_insert_of_notMem (parent_not_child r p), children_union]
  omega

/--
@isnad1 id=le.0h5v.s6.7d29b205d075 from=translated src=- shape=2c2b01de vocab=a4df754f
-/
theorem pages_subset_family (p : {T // T ∈ c.rest}) :
    pages r p ⊆ trianglesOn c.remainingEdges := by
  intro T hT
  rcases (mem_pages r).mp hT with rfl | ⟨hTc, _⟩
  · exact c.rest_packing.1 p.property
  · exact c.specialFamily_subset_triangles (child_actual r hTc)

/--
@isnad1 id=mem.4h7v.s7.defe9a8f8b14 from=translated src=- shape=b05eb84d vocab=640e3ffb
-/
theorem second_third_overlap_red {T U : Finset (Sym2 V)}
    (hT : T ∈ r.second) (hU : U ∈ r.third) {e : Sym2 V}
    (heT : e ∈ T) (heU : e ∈ U) : e ∈ c.newEdges := by
  by_contra heN
  have hd := (mem_residual.mp (r.third_maximum.1.1 hU)).2
  exact disjoint_left.mp hd heU
    (mem_blueEdges.mpr ⟨mem_support.mpr ⟨T, hT, heT⟩, heN⟩)

/--
@isnad1 id=eq.4h7v.s8.b4de93447c20 from=translated src=- shape=49589219 vocab=ba09d5d2
-/
theorem overlapping_children_red_eq {T U : Finset (Sym2 V)}
    (hT : T ∈ r.second ∪ r.third) (hU : U ∈ r.second ∪ r.third)
    {e : Sym2 V} (heT : e ∈ T) (heU : e ∈ U) :
    T ∩ c.newEdges = U ∩ c.newEdges := by
  have hTc := child_actual r hT
  have hUc := child_actual r hU
  rcases mem_union.mp hT with hT | hT <;> rcases mem_union.mp hU with hU | hU
  · by_cases h : T = U
    · rw [h]
    · exact (disjoint_left.mp (r.second_maximum.1.2 hT hU h) heT heU).elim
  · have heN := second_third_overlap_red r hT hU heT heU
    exact (c.specialFamily_colored.red_eq_singleton hTc heT heN).trans
      (c.specialFamily_colored.red_eq_singleton hUc heU heN).symm
  · have heN := second_third_overlap_red r hU hT heU heT
    exact (c.specialFamily_colored.red_eq_singleton hTc heT heN).trans
      (c.specialFamily_colored.red_eq_singleton hUc heU heN).symm
  · by_cases h : T = U
    · rw [h]
    · exact (disjoint_left.mp (r.third_maximum.1.2 hT hU h) heT heU).elim

/--
@isnad1 id=le.0h5v.s7.a1fd05c05ea6 from=translated src=- shape=c4f1260f vocab=77b6b2b4
-/
theorem book_inter_rest_subset (p : {T // T ∈ c.rest}) :
    support (pages r p) ∩ support c.rest ⊆ p.val := by
  intro e he
  obtain ⟨heb, heP⟩ := mem_inter.mp he
  obtain ⟨T, hT, heT⟩ := mem_support.mp heb
  rcases (mem_pages r).mp hT with rfl | ⟨hTc, hTR⟩
  · exact heT
  · have heR : e ∈ T ∩ c.newEdges :=
      special_inter_rest (child_actual r hTc) ▸ mem_inter.mpr ⟨heT, heP⟩
    exact (mem_inter.mp (hTR ▸ heR)).1

/--
@isnad1 id=disjoint.0h4v.s6.f62b7b6b4973 from=translated src=- shape=97cc652e vocab=d5a41174
-/
theorem supports_disjoint : Books.DisjointSupports (pages r) := by
  intro p p' hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  have hd := c.rest_packing.2 p.property p'.property hval
  apply disjoint_left.mpr
  intro e he he'
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  obtain ⟨U, hU, heU⟩ := mem_support.mp he'
  rcases (mem_pages r).mp hT with rfl | ⟨hTc, hTR⟩
  · have hep' := book_inter_rest_subset r p'
      (mem_inter.mpr ⟨he', mem_support.mpr ⟨p.val, p.property, heT⟩⟩)
    exact disjoint_left.mp hd heT hep'
  · rcases (mem_pages r).mp hU with rfl | ⟨hUc, hUR⟩
    · have hep := book_inter_rest_subset r p
        (mem_inter.mpr ⟨he, mem_support.mpr ⟨p'.val, p'.property, heU⟩⟩)
      exact disjoint_left.mp hd hep heU
    · exact hne (owner_unique (child_actual r hTc) p p' hTR
        ((overlapping_children_red_eq r hTc hUc heT heU).trans hUR))

/--
@isnad1 id=pairwise.1h4v.s8.bf623ea83330 from=translated src=- shape=50d912f5 vocab=0e92514d
-/
theorem children_pairwise_disjoint {K : Finset (Finset (Sym2 V))}
    (hK : K ⊆ c.specialFamily) :
    Pairwise (fun p p' : {T // T ∈ c.rest} =>
      Disjoint (Layered.children c.newEdges K p.val) (Layered.children c.newEdges K p'.val)) := by
  intro p p' hne
  apply disjoint_left.mpr
  intro T hT hT'
  obtain ⟨hTK, hTp⟩ := Layered.mem_children.mp hT
  exact hne (owner_unique (hK hTK) p p' hTp (Layered.mem_children.mp hT').2)

/--
@isnad1 id=eq.1h4v.s8.0295a94c69a2 from=translated src=- shape=08202812 vocab=464d9dd0
-/
theorem children_biUnion {K : Finset (Finset (Sym2 V))} (hK : K ⊆ c.specialFamily) :
    univ.biUnion (fun p : {T // T ∈ c.rest} => Layered.children c.newEdges K p.val) = K := by
  ext T
  constructor
  · intro hT
    obtain ⟨p, _, hp⟩ := mem_biUnion.mp hT
    exact (Layered.mem_children.mp hp).1
  · intro hT
    obtain ⟨p, hp⟩ := exists_parent (hK hT)
    exact mem_biUnion.mpr ⟨p, mem_univ _, Layered.mem_children.mpr ⟨hT, hp⟩⟩

/--
@isnad1 id=eq.1h4v.s7.ffcf4d0ce4e3 from=translated src=- shape=e8a66c2e vocab=1d01390d
-/
theorem sum_children_card {K : Finset (Finset (Sym2 V))} (hK : K ⊆ c.specialFamily) :
    (∑ p : {T // T ∈ c.rest}, (Layered.children c.newEdges K p.val).card) = K.card := by
  conv_rhs => rw [← children_biUnion hK]
  symm
  apply card_biUnion
  intro p _ p' _ hne
  exact children_pairwise_disjoint hK hne

/--
@isnad1 id=eq.0h4v.s7.85ed76508c26 from=translated src=- shape=a19666be vocab=065e1df9
-/
theorem sum_pages_card : (∑ p : {T // T ∈ c.rest}, (pages r p).card) =
    c.rest.card + r.second.card + r.third.card := by
  have hc (p : {T // T ∈ c.rest}) : (pages r p).card =
      (Layered.children c.newEdges (r.second ∪ r.third) p.val).card + 1 :=
    card_insert_of_notMem (parent_not_child r p)
  have hsub : r.second ∪ r.third ⊆ c.specialFamily := fun _ hT => child_actual r hT
  calc
    (∑ p : {T // T ∈ c.rest}, (pages r p).card) =
        ∑ p : {T // T ∈ c.rest},
          ((Layered.children c.newEdges (r.second ∪ r.third) p.val).card + 1) :=
      sum_congr rfl (fun p _ => hc p)
    _ = c.rest.card + r.second.card + r.third.card := by
      rw [sum_add_distrib, sum_children_card hsub, card_union_of_disjoint (second_third_disjoint r)]
      simp [Nat.add_comm, Nat.add_left_comm]

/--
@isnad1 id=iff.0h4v.s7.960b768c5f07 from=translated src=- shape=3de72cc1 vocab=e38b5789
-/
theorem parent_typeTwo_iff_red_nonempty (p : {T // T ∈ c.rest}) :
    p.val ∈ c.typeTwo ↔ (p.val ∩ c.newEdges).Nonempty := by
  constructor
  · intro hp
    exact Construction.typeTwo_red_nonempty (c := c) ⟨p.val, hp⟩
  · rintro ⟨e, he⟩
    have hactual := c.rest_packing.1 p.property
    refine mem_inter.mpr ⟨p.property, ?_⟩
    exact new_edge_forces_typeTwo hactual (c.remaining_old_ge_two hactual)
      (mem_sdiff.mpr ⟨(mem_inter.mp he).1, (mem_sdiff.mp (mem_inter.mp he).2).2⟩)

/--
@isnad1 id=iff.1h6v.s7.cec774b8d8c4 from=translated src=- shape=b26afd4a vocab=9fba62a5
-/
theorem page_typeTwo_iff_parent (p : {T // T ∈ c.rest}) {T : Finset (Sym2 V)}
    (hT : T ∈ pages r p) :
    T ∈ typeFamily c.remainingEdges c.old 2 ↔ p.val ∈ c.typeTwo := by
  rcases (mem_pages r).mp hT with rfl | ⟨hTc, hTR⟩
  · exact ⟨fun h => mem_inter.mpr ⟨p.property, h⟩, fun h => (mem_inter.mp h).2⟩
  · have hc := child_actual r hTc
    have hp : p.val ∈ c.typeTwo := by
      apply (parent_typeTwo_iff_red_nonempty p).mpr
      rw [← hTR]
      exact card_pos.mp (by rw [(c.specialFamily_colored T hc).2]; decide)
    exact ⟨fun _ => hp, fun _ => c.specialFamily_subset_typeTwo hc⟩

/--
@isnad1 id=ex.0h5v.s6.7609075c1fce from=translated src=- shape=57da7188 vocab=d3c19097
-/
theorem pages_common_edge (p : {T // T ∈ c.rest}) :
    ∃ e, ∀ T ∈ pages r p, e ∈ T := by
  by_cases hn : (p.val ∩ c.newEdges).Nonempty
  · obtain ⟨e, he⟩ := hn
    refine ⟨e, ?_⟩
    intro T hT
    rcases (mem_pages r).mp hT with rfl | ⟨_, hTR⟩
    · exact (mem_inter.mp he).1
    · exact (mem_inter.mp (hTR.symm ▸ he)).1
  · obtain ⟨e, he⟩ := trianglesOn_nonempty (c.rest_packing.1 p.property)
    refine ⟨e, ?_⟩
    intro T hT
    rcases (mem_pages r).mp hT with rfl | ⟨hTc, hTR⟩
    · exact he
    · have hred : (T ∩ c.newEdges).Nonempty :=
        card_pos.mp (by rw [(c.specialFamily_colored T (child_actual r hTc)).2]; decide)
      exact (hn (hTR ▸ hred)).elim

/--
@isnad1 id=ispackin.1h5v.s7.41fb4631f8ca from=translated src=- shape=f2c74c96 vocab=f8362cca
-/
theorem choices_packing {f : {T // T ∈ c.rest} → Finset (Sym2 V)}
    (hf : Books.ChoosesPages (pages r) f) :
    IsPacking (trianglesOn c.remainingEdges) (Books.choice f) :=
  Books.choice_isPacking (pages_subset_family r) (supports_disjoint r) hf

/--
@isnad1 id=eq.1h5v.s7.8f17c6873f3d from=translated src=- shape=a9d7d676 vocab=bc9bbdce
-/
theorem choices_card {f : {T // T ∈ c.rest} → Finset (Sym2 V)}
    (hf : Books.ChoosesPages (pages r) f) : (Books.choice f).card = c.rest.card := by
  simpa using Books.card_choice (supports_disjoint r)
    (fun p T hT => trianglesOn_nonempty (pages_subset_family r p hT)) hf

/-- A full choice preserves exactly the original set of type-two parent slots.
@isnad1 id=eq.1h5v.s7.930bcae1039c from=translated src=- shape=e27c5366 vocab=0d59462d
-/
theorem choices_typeTwo_card {f : {T // T ∈ c.rest} → Finset (Sym2 V)}
    (hf : Books.ChoosesPages (pages r) f) :
    (Books.choice f ∩ typeFamily c.remainingEdges c.old 2).card = c.typeTwo.card := by
  classical
  have heq : Books.choice f ∩ typeFamily c.remainingEdges c.old 2 =
      univ.image (fun p : {T // T ∈ c.typeTwo} =>
        f ⟨p.val, c.typeTwo_subset_rest p.property⟩) := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTf, hTtype⟩ := mem_inter.mp hT
      obtain ⟨p, rfl⟩ := Books.mem_choice.mp hTf
      have hp := (page_typeTwo_iff_parent r p (hf p)).mp hTtype
      exact mem_image.mpr ⟨⟨p.val, hp⟩, mem_univ _, rfl⟩
    · intro hT
      obtain ⟨p, _, rfl⟩ := mem_image.mp hT
      exact mem_inter.mpr
        ⟨Books.mem_choice.mpr ⟨⟨p.val, c.typeTwo_subset_rest p.property⟩, rfl⟩,
          (page_typeTwo_iff_parent r ⟨p.val, c.typeTwo_subset_rest p.property⟩
            (hf ⟨p.val, c.typeTwo_subset_rest p.property⟩)).mpr p.property⟩
  have hfInj := Books.choice_injective (supports_disjoint r)
    (fun p T hT => trianglesOn_nonempty (pages_subset_family r p hT)) hf
  have hgInj : Function.Injective (fun p : {T // T ∈ c.typeTwo} =>
      f ⟨p.val, c.typeTwo_subset_rest p.property⟩) := by
    intro p p' h
    exact Subtype.ext (congrArg (fun q : {T // T ∈ c.rest} => q.val) (hfInj h))
  rw [heq, card_image_of_injective _ hgInj]
  simp

/-- Full choices preserve both counts in the lexicographic maximum.
@isnad1 id=islexmax.1h5v.s7.36004175e843 from=translated src=- shape=71ce8cee vocab=f8e613f6
-/
theorem choices_lexMaximum {f : {T // T ∈ c.rest} → Finset (Sym2 V)}
    (hf : Books.ChoosesPages (pages r) f) :
    IsLexMaximumPacking (trianglesOn c.remainingEdges)
      (typeFamily c.remainingEdges c.old 2) (Books.choice f) := by
  apply c.rest_lexMaximum.of_same_counts (choices_packing r hf)
  · exact choices_typeTwo_card r hf
  · exact choices_card r hf

/--
@isnad1 id=everycho.0h4v.s6.51f11d938cec from=translated src=- shape=a6a05ac2 vocab=06b14905
-/
theorem everyChoiceMeets :
    Books.EveryChoiceMeets (trianglesOn c.remainingEdges) (pages r) := by
  intro f hf T hT
  obtain ⟨e, he⟩ := (choices_lexMaximum r hf).meets_support hT (trianglesOn_nonempty hT)
  obtain ⟨U, hU, heU⟩ := mem_support.mp (mem_inter.mp he).2
  obtain ⟨p, rfl⟩ := Books.mem_choice.mp hU
  refine ⟨p, ?_⟩
  intro hd
  exact disjoint_left.mp hd (mem_inter.mp he).1 heU

/-- The actual third cover of the remaining graph, with all three layers paid.
@isnad1 id=ex.0h4v.s6.d5e22f8b6e3b from=translated src=- shape=edab8621 vocab=faf287c9
-/
theorem exists_third_cover :
    ∃ C : Finset (Sym2 V), IsCover (trianglesOn c.remainingEdges) C ∧
      C.card + r.second.card + r.third.card ≤ 3 * c.rest.card := by
  obtain ⟨C, hC, hcard⟩ := exists_cover_of_small_common_spine_books
    (trianglesOn c.remainingEdges) (pages r) (pages_nonempty r) (pages_card_le_three r)
    (fun p T hT => (mem_trianglesOn.mp (pages_subset_family r p hT)).1)
    (pages_common_edge r) (fun _ hT => (mem_trianglesOn.mp hT).1) (everyChoiceMeets r)
  rw [sum_pages_card r] at hcard
  simp only [Fintype.card_coe] at hcard
  exact ⟨C, hC, by omega⟩

end ThreeLayer
end Tuza

namespace Tuza
namespace Construction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)} (c : Construction edges)

/-- The book cover of G' together with the deleted first packing covers G.
@isnad1 id=ex.0h4v.s6.584705289944 from=translated src=- shape=d9fe2e97 vocab=5b9027e7
-/
theorem exists_full_book_cover (r : RefinedConstruction c) :
    ∃ C, IsCover (trianglesOn edges) C ∧
      C.card + r.second.card + r.third.card ≤ 3 * c.initial.card := by
  obtain ⟨D, hD, hc⟩ := ThreeLayer.exists_third_cover r
  have hres : IsCover (residual (trianglesOn edges) (support c.first)) D := by
    rw [← trianglesOn_sdiff]
    exact hD
  refine ⟨support c.first ∪ D, cover_union_residual hres, ?_⟩
  have hsize := c.first_packing.card_support_uniform
    (fun _ hT => trianglesOn_card (c.first_packing.1 hT))
  have hu := card_union_le (support c.first) D
  have hp := c.first_rest_card_le
  omega

/--
@isnad1 id=le.0h4v.s6.adf3fb8f6fd5 from=translated src=- shape=39c74ab6 vocab=6c105edd
-/
theorem full_book_cover (r : RefinedConstruction c) :
    transversalNumber (trianglesOn edges) + r.second.card + r.third.card ≤
      3 * c.initial.card := by
  obtain ⟨C, hC, hc⟩ := c.exists_full_book_cover r
  have ht := hC.number_le
  omega

end Construction
end Tuza
