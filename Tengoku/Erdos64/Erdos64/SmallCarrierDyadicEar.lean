import Tengoku.Erdos64.Erdos64.BoundaryRootForcing
import Tengoku.Erdos64.Erdos64.BoundaryRootCyclePath
import Tengoku.Erdos64.Erdos64.PortSuppressionOddCycle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A cycle through a synthetic boundary root lifts to a fresh dyadic ear
in the original graph. If its two external attachments coincided, the lift
would already be a forbidden dyadic cycle.-/
theorem boundaryRoot_dyadic_cycle_ear
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (K : Finset V) (S : Set V)
    (hnoG : ¬ HasPowerOfTwoCycle G)
    (hdisjoint : ∀ v, v ∈ K → v ∉ S)
    (hboundary : ∀ v, v ∈ K → ∀ w, w ∉ K → G.Adj v w → w ∈ S)
    (hyes : HasPowerOfTwoCycle
      (boundaryRootGraph (G.induce (↑K : Set V)) (carrierBoundaryVertices G K))) :
    ∃ k : ℕ, ∃ a b : V, ∃ ear : G.Walk a b,
      2 ≤ k ∧ a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ear.IsPath ∧ ear.length = 2 ^ k ∧
      (∀ v, v ∈ ear.support → v = a ∨ v = b ∨ v ∈ K) ∧
      (∀ v, v ∈ ear.support → v ∈ S → v = a ∨ v = b) := by
  classical
  let H := G.induce (↑K : Set V)
  let B := carrierBoundaryVertices G K
  have hno : ¬ HasPowerOfTwoCycle H :=
    not_hasPowerOfTwoCycle_induce_of_not_hasPowerOfTwoCycle hnoG
  obtain ⟨k, a, b, q, hk, ha, hb, hab, hq, hlen⟩ :=
    boundaryRoot_dyadic_cycle_path B hno hyes
  obtain ⟨aOut, haOut, haa⟩ := (mem_carrierBoundaryVertices G K a).mp ha
  obtain ⟨bOut, hbOut, hbb⟩ := (mem_carrierBoundaryVertices G K b).mp hb
  have haS := hboundary a.1 a.2 aOut haOut haa
  have hbS := hboundary b.1 b.2 bOut hbOut hbb
  let e : H ↪g G := SimpleGraph.Embedding.induce (↑K : Set V)
  let p : G.Walk a.1 b.1 := q.map e.toHom
  have hp : p.IsPath := hq.map e.injective
  have hpK : ∀ v, v ∈ p.support → v ∈ K := by
    intro v hv
    change v ∈ (q.map e.toHom).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
    exact w.2
  have hplen : p.length + 2 = 2 ^ k := by
    change (q.map e.toHom).length + 2 = 2 ^ k
    rw [SimpleGraph.Walk.length_map]
    exact hlen
  have haavoid : aOut ∉ p.support := fun h => haOut (hpK aOut h)
  have hbavoid : bOut ∉ p.support := fun h => hbOut (hpK bOut h)
  have habOut : aOut ≠ bOut := by
    intro heq
    subst bOut
    obtain ⟨c, hc, hclen⟩ := cycle_based_at_fresh_vertex p hp
      (fun h => hab (Subtype.ext h)) haa.symm hbb.symm haavoid
    exact hnoG ⟨k, aOut, c, hk, hc, hclen.trans hplen⟩
  let ear : G.Walk aOut bOut := .cons haa.symm (p.concat hbb)
  have hear : ear.IsPath := by
    apply SimpleGraph.Walk.IsPath.cons (hp.concat hbavoid hbb)
    simp only [SimpleGraph.Walk.support_concat,
      List.mem_append, List.mem_singleton]
    exact fun h => h.elim haavoid habOut
  have hsupport : ∀ v, v ∈ ear.support → v = aOut ∨ v = bOut ∨ v ∈ K := by
    intro v hv
    simp only [ear, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (hpK v h))
    · exact Or.inr (Or.inl h)
  refine ⟨k, aOut, bOut, ear, by omega, haS, hbS, habOut, hear, ?_, hsupport, ?_⟩
  · simp only [ear, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat]
    omega
  · intro v hv hvS
    rcases hsupport v hv with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hdisjoint v h hvS).elim

/-- A nonempty region smaller than half a minimal counterexample forces an
ear of power-of-two length between distinct vertices on its boundary.
The interior lies in the region. No bound on the attachment separation is
asserted.-/
theorem MinimalCounterexample.small_carrier_dyadic_ear
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V) (S : Set V)
    (hK : K.Nonempty)
    (hdisjoint : ∀ v, v ∈ K → v ∉ S)
    (hboundary : ∀ v, v ∈ K → ∀ w, w ∉ K → G.Adj v w → w ∈ S)
    (hsize : 2 * K.card + 1 < Fintype.card V) :
    ∃ k : ℕ, ∃ a b : V, ∃ ear : G.Walk a b,
      1 ≤ k ∧ a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ear.IsPath ∧ ear.length = 2 ^ k ∧
      (∀ v, v ∈ ear.support → v = a ∨ v = b ∨ v ∈ K) ∧
      (∀ v, v ∈ ear.support → v ∈ S → v = a ∨ v = b) := by
  classical
  by_cases htwo : ∃ v ∈ K, ∃ a, a ∉ K ∧ ∃ b, b ∉ K ∧
      a ≠ b ∧ G.Adj v a ∧ G.Adj v b
  · obtain ⟨v, hv, a, haK, b, hbK, hab, hva, hvb⟩ := htwo
    let ear : G.Walk a b := .cons hva.symm (.cons hvb .nil)
    have hear : ear.IsPath := by
      apply SimpleGraph.Walk.IsPath.cons
      · exact SimpleGraph.Walk.IsPath.of_adj hvb
      · simp [hva.ne.symm, hab]
    have hsupport : ∀ w, w ∈ ear.support → w = a ∨ w = b ∨ w ∈ K := by
      intro w hw
      simp only [ear, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hv)
      · exact Or.inr (Or.inl rfl)
    refine ⟨1, a, b, ear, by omega, hboundary v hv a haK hva,
      hboundary v hv b hbK hvb, hab, hear, by rfl, hsupport, ?_⟩
    intro w hw hwS
    rcases hsupport w hw with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hdisjoint w h hwS).elim
  have hsingle : ∀ v, v ∈ K → ∀ a, a ∉ K → ∀ b, b ∉ K →
      G.Adj v a → G.Adj v b → a = b := by
    intro v hv a ha b hb hva hvb
    by_contra hab
    exact htwo ⟨v, hv, a, ha, b, hb, hab, hva, hvb⟩
  let H := G.induce (↑K : Set V)
  let B := carrierBoundaryVertices G K
  let R := boundaryRootGraph H B
  have hdeg : ∀ v, R.degree (some v) = G.degree v.1 := by
    intro v
    rw [boundaryRootGraph_degree_some]
    exact carrier_degree_add_boundary_indicator (G := G) K hsingle v
  have hroot : 2 ≤ R.degree none := by
    rw [boundaryRootGraph_degree_none]
    exact M.small_carrier_boundary_card_ge_two K hK hsingle hsize
  have hothers : ∀ v, v ≠ none → 3 ≤ R.degree v := by
    intro v hv
    cases v with
    | none => exact (hv rfl).elim
    | some v =>
        rw [hdeg]
        exact degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 v.1
  have hsmall : 2 * Fintype.card (Option (↑K : Set V)) - 1 < Fintype.card V := by
    simpa using (show 2 * (K.card + 1) - 1 < Fintype.card V by omega)
  have hyes := M.one_defect_small_has_dyadic_cycle none hroot hothers hsmall
  obtain ⟨k, a, b, ear, hk, hrest⟩ :=
    boundaryRoot_dyadic_cycle_ear K S M.isCounterexample.2
      hdisjoint hboundary hyes
  exact ⟨k, a, b, ear, by omega, hrest⟩

/-- Three boundary vertices make the new root have degree at least three,
so the dyadic-ear construction needs only the carrier-plus-root order bound.
The carrier need not be smaller than half the ambient graph.-/
theorem MinimalCounterexample.carrier_dyadic_ear_of_three_boundary
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V) (S : Set V)
    (hdisjoint : ∀ v, v ∈ K → v ∉ S)
    (hboundary : ∀ v, v ∈ K → ∀ w, w ∉ K → G.Adj v w → w ∈ S)
    (hsingle : ∀ v, v ∈ K → ∀ a, a ∉ K → ∀ b, b ∉ K →
      G.Adj v a → G.Adj v b → a = b)
    (hB : 3 ≤ (carrierBoundaryVertices G K).card)
    (hsize : K.card + 1 < Fintype.card V) :
    ∃ k : ℕ, ∃ a b : V, ∃ ear : G.Walk a b,
      2 ≤ k ∧ a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ear.IsPath ∧ ear.length = 2 ^ k ∧
      (∀ v, v ∈ ear.support → v = a ∨ v = b ∨ v ∈ K) ∧
      (∀ v, v ∈ ear.support → v ∈ S → v = a ∨ v = b) := by
  exact boundaryRoot_dyadic_cycle_ear K S M.isCounterexample.2
    hdisjoint hboundary
    (M.boundary_root_has_dyadic_cycle_of_three_boundary K hsingle hB hsize)

end Erdos64
