import Tengoku.TdaLib.TDA.Filtration.FilterFunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Ordering equivalence of face-value filtrations

`OrderingEquivalent f g` records agreement of every weak comparison between face
values, in both directions. The public characterization identifies this relation exactly
with an order isomorphism between the attained ranges that sends each face value to its
corresponding value. The order isomorphism is existential theory data; no selected map or
executable representative is part of this API.

Sublevels correspond at matched attained grades. This result does not identify arbitrary
ambient-threshold families or provide an extension between the full grade types.
-/

universe u v w z

namespace TDA.Filtration

variable {V : Type u} {α : Type v} {β : Type w} {γ : Type z}
variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]
variable {K : PreAbstractSimplicialComplex V}

/-- Two face-value filters have exactly the same weak order comparisons on every pair of
faces. The grade types may differ, and ties are preserved in both directions.-/
def OrderingEquivalent (f : FilterFunction K α) (g : FilterFunction K β) : Prop :=
  ∀ s t : TDA.Simplicial.TotalFace K,
    f.value s ≤ f.value t ↔ g.value s ≤ g.value t

namespace OrderingEquivalent

variable {f : FilterFunction K α} {g : FilterFunction K β}
variable {h : FilterFunction K γ}

/-- Ordering equivalence is reflexive.
@isnad1 id=ordering.0h4v.s4.24cf27ba8462 from=translated src=- shape=e7da5a2e vocab=a9cad7cf
-/
theorem refl (f : FilterFunction K α) : OrderingEquivalent f f := by
  intro s t
  rfl

/-- Ordering equivalence is symmetric, including across different grade types.
@isnad1 id=ordering.1h6v.s5.9a4b6808b579 from=translated src=- shape=f683ba6d vocab=a9cad7cf
-/
theorem symm (hfg : OrderingEquivalent f g) : OrderingEquivalent g f := by
  intro s t
  exact (hfg s t).symm

/-- Ordering equivalence composes across three independently universe-polymorphic grade types.
@isnad1 id=ordering.2h8v.s6.e65fc3c9b1cf from=translated src=- shape=08da7e0b vocab=a9cad7cf
-/
theorem trans (hfg : OrderingEquivalent f g) (hgh : OrderingEquivalent g h) :
    OrderingEquivalent f h := by
  intro s t
  exact (hfg s t).trans (hgh s t)

/-- Ordering equivalence identifies exactly the same tied pairs of faces.
@isnad1 id=iff.1h8v.s6.4e0098f6646b from=translated src=- shape=534c9f47 vocab=5215bbbd
-/
theorem value_eq_iff (hfg : OrderingEquivalent f g)
    (s t : TDA.Simplicial.TotalFace K) :
    f.value s = f.value t ↔ g.value s = g.value t := by
  constructor
  · intro he
    apply le_antisymm
    · exact (hfg s t).mp he.le
    · exact (hfg t s).mp he.ge
  · intro he
    apply le_antisymm
    · exact (hfg s t).mpr he.le
    · exact (hfg t s).mpr he.ge

/-- Sublevels at corresponding attained grades are equal as preabstract complexes.
@isnad1 id=eq.1h7v.s6.7cbcef713c70 from=translated src=- shape=2443bb9d vocab=a7c439c7
-/
theorem sublevel_eq (hfg : OrderingEquivalent f g)
    (s : TDA.Simplicial.TotalFace K) :
    f.sublevel (f.value s) = g.sublevel (g.value s) := by
  apply le_antisymm
  · intro t ht
    obtain ⟨htK, hle⟩ := (f.mem_sublevel_iff _ _).mp ht
    exact (g.mem_sublevel_iff _ _).mpr
      ⟨htK, (hfg ⟨t, htK⟩ s).mp hle⟩
  · intro t ht
    obtain ⟨htK, hle⟩ := (g.mem_sublevel_iff _ _).mp ht
    exact (f.mem_sublevel_iff _ _).mpr
      ⟨htK, (hfg ⟨t, htK⟩ s).mpr hle⟩

end OrderingEquivalent

/-- Ordering equivalence is equivalent to an order isomorphism of the attained value ranges
that maps each face's value to the other filter's value on that same face.
@isnad1 id=iff.0h6v.s9.d34d7305f379 from=translated src=- shape=ee16f736 vocab=6df1d093
-/
theorem orderingEquivalent_iff_exists_rangeOrderIso
    (f : FilterFunction K α) (g : FilterFunction K β) :
    OrderingEquivalent f g ↔
      ∃ e : Set.range f.value ≃o Set.range g.value,
        ∀ s : TDA.Simplicial.TotalFace K,
          (e ⟨f.value s, ⟨s, rfl⟩⟩).val = g.value s := by
  classical
  constructor
  · intro hfg
    let F : Set.range f.value → Set.range g.value := fun a =>
      ⟨g.value (Classical.choose a.property),
        ⟨Classical.choose a.property, rfl⟩⟩
    have hF (s : TDA.Simplicial.TotalFace K) :
        F ⟨f.value s, ⟨s, rfl⟩⟩ = ⟨g.value s, ⟨s, rfl⟩⟩ := by
      apply Subtype.ext
      apply (OrderingEquivalent.value_eq_iff hfg _ _).mp
      exact (Classical.choose_spec (show f.value s ∈ Set.range f.value from ⟨s, rfl⟩))
    have horder (a b : Set.range f.value) : F a ≤ F b ↔ a ≤ b := by
      rcases a with ⟨a, ⟨s, rfl⟩⟩
      rcases b with ⟨b, ⟨t, rfl⟩⟩
      simp only [hF]
      exact (hfg s t).symm
    let emb : Set.range f.value ↪o Set.range g.value :=
      OrderEmbedding.ofMapLEIff F horder
    have hsurj : Function.Surjective emb := by
      rintro ⟨b, ⟨s, rfl⟩⟩
      exact ⟨⟨f.value s, ⟨s, rfl⟩⟩, hF s⟩
    let e : Set.range f.value ≃o Set.range g.value := OrderIso.ofSurjective emb hsurj
    refine ⟨e, ?_⟩
    intro s
    exact congrArg Subtype.val (hF s)
  · rintro ⟨e, he⟩
    intro s t
    have hs := he s
    have ht := he t
    have hm := map_le_map_iff e
      (a := (⟨f.value s, ⟨s, rfl⟩⟩ : Set.range f.value))
      (b := (⟨f.value t, ⟨t, rfl⟩⟩ : Set.range f.value))
    change (e ⟨f.value s, ⟨s, rfl⟩⟩).val ≤
      (e ⟨f.value t, ⟨t, rfl⟩⟩).val ↔ f.value s ≤ f.value t at hm
    rw [hs, ht] at hm
    exact hm.symm

end TDA.Filtration
