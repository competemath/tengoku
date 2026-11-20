import Tengoku.Erdos64.Erdos64.RootDeletedAttachmentBound
import Tengoku.Erdos64.Erdos64.ComponentAttachmentLowerBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A degree-four root in a critical minimum-degree-three graph has exactly
    two components after deletion, and every native component has exactly two
    root attachments.
@isnad1 id=and.5h3v.s7.30146fbd04f3 from=translated src=- shape=fb7ea9d9 vocab=1483446c
-/
theorem rootDeleted_degree_four_exact_two_components
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (r : V)
    [Fintype ((G.induce {v : V | v ≠ r}).ConnectedComponent)]
    (hconn : G.Connected) (hmin : G.minDegree ≥ 3)
    (hcritical : IsSubgraphCritical G) (hdegree : G.degree r = 4)
    (hcomponents :
      2 ≤ Fintype.card ((G.induce {v : V | v ≠ r}).ConnectedComponent)) :
    Fintype.card ((G.induce {v : V | v ≠ r}).ConnectedComponent) = 2 ∧
      ∀ C : (G.induce {v : V | v ≠ r}).ConnectedComponent,
        (rootDeletedComponentAttachments G r C).card = 2 := by
  classical
  let Comp := (G.induce {v : V | v ≠ r}).ConnectedComponent
  have htwo : ∀ C : Comp,
      2 ≤ (rootDeletedComponentAttachments G r C).card := by
    intro C
    have hcarrier := rootDeletedComponentCarrier_nonempty_not_mem G r C
    have hboundary :
        ∀ x, x ∈ rootDeletedComponentCarrier G r C →
          ∀ y, y ∉ rootDeletedComponentCarrier G r C →
            G.Adj x y → y = r := by
      intro x hx y hy hxy
      rcases (rootDeletedComponent_boundary r hconn C).1 x hx y hxy with
        hyC | hyr
      · exact (hy hyC).elim
      · exact hyr
    have hlower := component_attachment_lower_bound hconn hmin hcritical
      (rootDeletedComponentCarrier G r C) r hcarrier.1 hcarrier.2 hboundary
    have hattach :
        rootDeletedComponentAttachments G r C =
          (rootDeletedComponentCarrier G r C).filter (G.Adj r) := by
      ext x
      simp [rootDeletedComponentAttachments,
        SimpleGraph.neighborFinset_eq_filter, and_comm]
    have hdegreebound :
        G.degree r ≤
          (rootDeletedComponentAttachments G r C).card + 2 := by
      simpa [hattach] using hlower.2
    omega
  have hpair :
      ((Finset.univ : Finset Comp) : Set Comp).PairwiseDisjoint
        (rootDeletedComponentAttachments G r) := by
    intro C _ D _ hCD
    exact rootDeletedComponentAttachments_pairwise_disjoint r hCD
  have hbi :
      (Finset.univ : Finset Comp).biUnion
          (rootDeletedComponentAttachments G r) = G.neighborFinset r := by
    have hbi₀ := rootDeletedComponentAttachments_biUnion (G := G) r
    rw [show (Finset.univ : Finset Comp) =
        (@Finset.univ Comp (Fintype.ofFinite _)) by
          ext x
          simp]
    exact hbi₀
  have hsum :
      (∑ C : Comp, (rootDeletedComponentAttachments G r C).card) = 4 := by
    calc
      (∑ C : Comp, (rootDeletedComponentAttachments G r C).card) =
          ((Finset.univ : Finset Comp).biUnion
            (rootDeletedComponentAttachments G r)).card := by
        rw [Finset.card_biUnion hpair]
      _ = (G.neighborFinset r).card := by rw [hbi]
      _ = 4 := by
        simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegree
  have hsumlower : 2 * Fintype.card Comp ≤
      ∑ C : Comp, (rootDeletedComponentAttachments G r C).card := by
    calc
      2 * Fintype.card Comp = ∑ _C : Comp, 2 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ C : Comp, (rootDeletedComponentAttachments G r C).card := by
        exact Finset.sum_le_sum (fun C _ => htwo C)
  have hcard : Fintype.card Comp = 2 := by
    rw [hsum] at hsumlower
    have hcomponentsComp : 2 ≤ Fintype.card Comp := by
      simpa [Comp] using hcomponents
    omega
  have hattach_two : ∀ C : Comp,
      (rootDeletedComponentAttachments G r C).card = 2 := by
    intro C
    have hsplit :
        (rootDeletedComponentAttachments G r C).card +
            (∑ D ∈ (Finset.univ.erase C),
              (rootDeletedComponentAttachments G r D).card) =
          ∑ D : Comp, (rootDeletedComponentAttachments G r D).card := by
      exact (Finset.univ : Finset Comp).add_sum_erase
        (fun D => (rootDeletedComponentAttachments G r D).card)
        (Finset.mem_univ C)
    have hcarderase : (Finset.univ.erase C : Finset Comp).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ C)]
      simp [hcard]
    have hrest : 2 ≤
      (∑ D ∈ (Finset.univ.erase C),
          (rootDeletedComponentAttachments G r D).card) := by
      calc
        2 = ∑ _D ∈ (Finset.univ.erase C), 2 := by
          simp [hcarderase]
        _ ≤ ∑ D ∈ (Finset.univ.erase C),
            (rootDeletedComponentAttachments G r D).card := by
          exact Finset.sum_le_sum (fun D _ => htwo D)
    rw [hsum] at hsplit
    have hle : (rootDeletedComponentAttachments G r C).card ≤ 2 := by
      omega
    exact le_antisymm hle (htwo C)
  constructor
  · simpa [Comp] using hcard
  · intro C
    simpa [Comp] using hattach_two C

/-- The same balance conclusion with the more geometric hypothesis that two
    distinct root-deleted components are supplied explicitly.
@isnad1 id=and.5h3v.s8.254f3668be93 from=translated src=- shape=1bff6889 vocab=e1e10fa9
-/
theorem rootDeleted_degree_four_exact_two_components_of_distinct
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (r : V)
    [Fintype ((G.induce {v : V | v ≠ r}).ConnectedComponent)]
    (hconn : G.Connected) (hmin : G.minDegree ≥ 3)
    (hcritical : IsSubgraphCritical G) (hdegree : G.degree r = 4)
    (hcomponents : ∃ C D : (G.induce {v : V | v ≠ r}).ConnectedComponent,
      C ≠ D) :
    Fintype.card ((G.induce {v : V | v ≠ r}).ConnectedComponent) = 2 ∧
      ∀ C : (G.induce {v : V | v ≠ r}).ConnectedComponent,
        (rootDeletedComponentAttachments G r C).card = 2 := by
  classical
  have hcard :
      2 ≤ Fintype.card ((G.induce {v : V | v ≠ r}).ConnectedComponent) := by
    obtain ⟨C, D, hCD⟩ := hcomponents
    have hsub :
        ({C, D} : Finset ((G.induce {v : V | v ≠ r}).ConnectedComponent)) ⊆
          Finset.univ := by
      simp
    have hle := Finset.card_le_card hsub
    have hpair :
        ({C, D} : Finset ((G.induce {v : V | v ≠ r}).ConnectedComponent)).card =
          2 := by
      simp [hCD]
    rw [hpair] at hle
    exact hle
  exact rootDeleted_degree_four_exact_two_components r hconn hmin hcritical
    hdegree hcard

end Erdos64
