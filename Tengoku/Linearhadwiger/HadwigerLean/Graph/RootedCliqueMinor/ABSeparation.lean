import Tengoku.Linearhadwiger.HadwigerLean.Graph.SetMengerTheorem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Turning an A--B vertex cut into a graph separation

The near shore consists of vertices reachable from A after deleting Q.
Its boundary is exactly Q, even when the separator contains terminals.
-/

namespace HadwigerLean

namespace SetMenger

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (A Q : Finset V)

/-- Vertices reachable from A while avoiding Q.-/
def reachableSide : Set V :=
  {v | ∃ a : ↥((Q : Set V)ᶜ), (a : V) ∈ A ∧
    ∃ b : ↥((Q : Set V)ᶜ), (b : V) = v ∧
      (G.induce (Q : Set V)ᶜ).Reachable a b}

/--
@isnad1 id=disjoint.0h4v.s5.92a12250e2a6 from=translated src=- shape=fa83e06f vocab=1ca7c975
-/
theorem reachableSide_avoids_cut :
    Disjoint (reachableSide G A Q) (Q : Set V) := by
  apply Set.disjoint_left.mpr
  intro v hv hvQ
  obtain ⟨a, haA, b, rfl, hab⟩ := hv
  exact b.property hvQ

/--
@isnad1 id=mem.3h6v.s6.58e6d1f9370d from=translated src=- shape=e736b933 vocab=eb506cf6
-/
theorem reachableSide_closed {x y : V}
    (hx : x ∈ reachableSide G A Q)
    (hyQ : y ∉ Q) (hxy : G.Adj x y) :
    y ∈ reachableSide G A Q := by
  obtain ⟨a, haA, b, hb, hab⟩ := hx
  let c : ↥((Q : Set V)ᶜ) := ⟨y, hyQ⟩
  have hbc : (G.induce (Q : Set V)ᶜ).Adj b c := by
    change G.Adj b.1 y
    simpa only [hb] using hxy
  exact ⟨a, haA, c, rfl, hab.trans hbc.reachable⟩

/-- The near side together with Q, versus the complement of the near side.-/
def reachableSeparation : VertexSeparation G where
  left := reachableSide G A Q ∪ (Q : Set V)
  right := (reachableSide G A Q)ᶜ
  cover := by
    ext v
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases h : v ∈ reachableSide G A Q
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  no_cross := by
    intro x y hxL hxR hyR hyL hxy
    have hx : x ∈ reachableSide G A Q := by
      by_contra hn
      exact hxR hn
    have hyQ : y ∉ Q := by
      intro hyQ
      exact hyL (Or.inr hyQ)
    exact hyR (reachableSide_closed G A Q hx hyQ hxy)

/--
@isnad1 id=mem.1h5v.s5.8745522b93ec from=translated src=- shape=92a5d06d vocab=7a187ecf
-/
theorem reachableSeparation_left_of_mem (a : V) (ha : a ∈ A) :
    a ∈ (reachableSeparation G A Q).left := by
  by_cases hQ : a ∈ Q
  · exact Or.inr hQ
  · left
    let a' : ↥((Q : Set V)ᶜ) := ⟨a, hQ⟩
    exact ⟨a', ha, a', rfl, SimpleGraph.Reachable.refl _⟩

/--
@isnad1 id=mem.3h6v.s6.a323a94fc4d6 from=translated src=- shape=8252463c vocab=f3c5c6e4
-/
theorem reachableSeparation_strictRight_of_ABSeparator
    (B : Finset V) (hAB : IsABSeparator G A B Q)
    (b : V) (hb : b ∈ B) (hbQ : b ∉ Q) :
    b ∈ (reachableSeparation G A Q).strictRight := by
  have hnot : b ∉ reachableSide G A Q := by
    intro hnear
    obtain ⟨a, haA, c, hc, hac⟩ := hnear
    have hc' : c = (⟨b, hbQ⟩ : ↥((Q : Set V)ᶜ)) := Subtype.ext hc
    subst c
    let p : (G.induce (Q : Set V)ᶜ).Path a ⟨b, hbQ⟩ := hac.some.toPath
    let q : G.Path a.1 b :=
      p.mapEmbedding (SimpleGraph.Embedding.induce (Q : Set V)ᶜ)
    obtain ⟨v, hvQ, hvq⟩ := hAB a.1 haA b hb q
    have hvmap : v ∈ (p : (G.induce (Q : Set V)ᶜ).Walk a ⟨b, hbQ⟩).support.map Subtype.val := by
      change v ∈ ((p : (G.induce (Q : Set V)ᶜ).Walk a ⟨b, hbQ⟩).map
        (SimpleGraph.Embedding.induce (Q : Set V)ᶜ).toHom).support at hvq
      rw [SimpleGraph.Walk.support_map] at hvq
      simpa using hvq
    obtain ⟨z, _, hz⟩ := List.mem_map.mp hvmap
    exact z.property (hz ▸ hvQ)
  exact ⟨hnot, by
    intro hleft
    rcases hleft with hnear | hcut
    · exact hnot hnear
    · exact hbQ hcut⟩

/--
@isnad1 id=mem.2h6v.s5.0107ed41b155 from=translated src=- shape=dd567fec vocab=2f353ef6
-/
theorem reachableSeparation_right_of_ABSeparator
    (B : Finset V) (hAB : IsABSeparator G A B Q)
    (b : V) (hb : b ∈ B) :
    b ∈ (reachableSeparation G A Q).right := by
  by_cases hbQ : b ∈ Q
  · intro hnear
    exact (Set.disjoint_left.mp (reachableSide_avoids_cut G A Q)) hnear hbQ
  · exact (reachableSeparation_strictRight_of_ABSeparator G A Q B hAB b hb hbQ).1
end SetMenger

end HadwigerLean
