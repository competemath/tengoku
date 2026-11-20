import Tengoku.Erdos64.Erdos64.CutSidePathParity
import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Deleting the support of an even simple path from an even-order carrier
leaves an odd-order graph, hence at least one odd-order connected component.-/
theorem exists_odd_offPathComponent_of_even_card
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (A : Finset V) (hA : Even A.card) {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (heven : Even p.length)
    (hinside : ∀ v, v ∈ p.support → v ∈ A) :
    ∃ E : (G.induce {v : V | v ∈ A ∧ v ∉ p.support}).ConnectedComponent,
      Odd (offPathComponentCarrier G A p E).card := by
  classical
  let W := {v : V // v ∈ A ∧ v ∉ p.support}
  let H := G.induce {v : V | v ∈ A ∧ v ∉ p.support}
  have hsub : p.support.toFinset ⊆ A := by
    intro v hv
    exact hinside v (List.mem_toFinset.mp hv)
  have hpathcard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
  have hWcard : Fintype.card W = (A \ p.support.toFinset).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext v
    simp
  have hsum := Finset.card_sdiff_add_card_eq_card hsub
  rw [← hWcard, hpathcard] at hsum
  have hWodd : Odd (Fintype.card W) := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := heven
    exact ⟨a - b - 1, by omega⟩
  have hWodd' : Odd (Nat.card W) := by
    rwa [Nat.card_eq_fintype_card]
  have hodd : Odd H.oddComponents.ncard := H.odd_ncard_oddComponents.mpr hWodd'
  have hnonempty : H.oddComponents.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (fun h => Nat.not_odd_zero (h ▸ hodd))
  obtain ⟨E, hE⟩ := hnonempty
  refine ⟨E, ?_⟩
  have hcard : (offPathComponentCarrier G A p E).card = E.supp.ncard := by
    unfold offPathComponentCarrier
    rw [Finset.card_image_of_injective _ Subtype.val_injective,
      ← Set.ncard_eq_toFinset_card']
  rw [hcard]
  exact hE

/-- In an all-odd-degree cut side, every even simple path omits an entire
odd-order connected component, not merely an unspecified vertex.-/
theorem MinimalCounterexample.rootDeleted_even_path_odd_offPathComponent
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    (hodd : ∀ v, v ∈ rootDeletedComponentCarrier G r C → Odd (G.degree v))
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) (heven : Even p.length)
    (hinside : ∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C) :
    ∃ E : (G.induce {v : V | v ∈ rootDeletedComponentCarrier G r C ∧
      v ∉ p.support}).ConnectedComponent,
      Odd (offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E).card := by
  exact exists_odd_offPathComponent_of_even_card _
    (M.rootDeleted_cut_side_card_even_of_odd_degrees r C D hCD hodd)
    p hp heven hinside

end Erdos64
