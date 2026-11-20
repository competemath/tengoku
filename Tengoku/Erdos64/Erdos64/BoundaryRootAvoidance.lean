import Tengoku.Erdos64.Erdos64.SmallCarrierBoundary
import Tengoku.Erdos64.Erdos64.BoundaryRootCyclePath
import Tengoku.Erdos64.Erdos64.PortSuppressionOddCycle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- With at least four boundary vertices, omitting any one boundary-root
incidence leaves just one possible degree-two defect. Doubling there forces
a dyadic cycle while the synthetic root still has degree at least three.-/
theorem MinimalCounterexample.boundary_root_erase_has_dyadic_cycle
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V)
    (hsingle : ∀ v, v ∈ K → ∀ a, a ∉ K → ∀ b, b ∉ K →
      G.Adj v a → G.Adj v b → a = b)
    (hB : 4 ≤ (carrierBoundaryVertices G K).card)
    (hsize : 2 * K.card + 1 < Fintype.card V)
    (t : {v : V // v ∈ K}) :
    HasPowerOfTwoCycle (boundaryRootGraph (G.induce (↑K : Set V))
      ((carrierBoundaryVertices G K).erase t)) := by
  classical
  let H := G.induce (↑K : Set V)
  let B := carrierBoundaryVertices G K
  let R := boundaryRootGraph H (B.erase t)
  have haccount := carrier_degree_add_boundary_indicator K hsingle
  have htdegree : 2 ≤ R.degree (some t) := by
    rw [boundaryRootGraph_degree_some]
    simp only [Finset.notMem_erase, ↓reduceIte, Nat.add_zero]
    change 2 ≤ (G.induce (↑K : Set V)).degree t
    have ht := haccount t
    have hmin := degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 t.1
    split_ifs at ht <;> omega
  have hroot : 3 ≤ R.degree none := by
    rw [boundaryRootGraph_degree_none]
    have hB' : 4 ≤ B.card := hB
    by_cases ht : t ∈ B
    · rw [Finset.card_erase_of_mem ht]
      omega
    · rw [Finset.erase_eq_of_notMem ht]
      omega
  have hother : ∀ v, v ≠ some t → 3 ≤ R.degree v := by
    intro v hv
    cases v with
    | none => exact hroot
    | some v =>
      have hvt : v ≠ t := fun h => hv (congrArg some h)
      rw [boundaryRootGraph_degree_some]
      change 3 ≤ (G.induce (↑K : Set V)).degree v +
        (if v ∈ (carrierBoundaryVertices G K).erase t then 1 else 0)
      have hmem : v ∈ (carrierBoundaryVertices G K).erase t ↔
          v ∈ carrierBoundaryVertices G K := by
        exact ⟨fun h => (Finset.mem_erase.mp h).2,
          fun h => Finset.mem_erase.mpr ⟨hvt, h⟩⟩
      rw [if_congr hmem rfl rfl]
      rw [haccount]
      exact degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 v.1
  have horder : 2 * Fintype.card (Option (↑K : Set V)) - 1 < Fintype.card V := by
    simpa using (show 2 * (K.card + 1) - 1 < Fintype.card V by omega)
  exact M.one_defect_small_has_dyadic_cycle (some t) htdegree hother horder

/-- A carrier with at least four boundary vertices has a forced dyadic
boundary path avoiding any one specified vertex at both ends. The path may
still contain that vertex internally.-/
theorem MinimalCounterexample.carrier_boundary_path_avoiding
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V)
    (hsingle : ∀ v, v ∈ K → ∀ a, a ∉ K → ∀ b, b ∉ K →
      G.Adj v a → G.Adj v b → a = b)
    (hB : 4 ≤ (carrierBoundaryVertices G K).card)
    (hsize : 2 * K.card + 1 < Fintype.card V)
    (t : {v : V // v ∈ K}) :
    ∃ k : ℕ, ∃ a b : {v : V // v ∈ K},
      ∃ p : (G.induce (↑K : Set V)).Walk a b,
        2 ≤ k ∧ a ∈ carrierBoundaryVertices G K ∧
        b ∈ carrierBoundaryVertices G K ∧ a ≠ t ∧ b ≠ t ∧
        a ≠ b ∧ p.IsPath ∧ p.length + 2 = 2 ^ k := by
  classical
  have hno : ¬ HasPowerOfTwoCycle (G.induce (↑K : Set V)) :=
    not_hasPowerOfTwoCycle_induce_of_not_hasPowerOfTwoCycle M.isCounterexample.2
  have hyes := M.boundary_root_erase_has_dyadic_cycle K hsingle hB hsize t
  obtain ⟨k, a, b, p, hk, ha, hb, hab, hp, hlen⟩ :=
    boundaryRoot_dyadic_cycle_path ((carrierBoundaryVertices G K).erase t) hno hyes
  exact ⟨k, a, b, p, hk, (Finset.mem_erase.mp ha).2,
    (Finset.mem_erase.mp hb).2, (Finset.mem_erase.mp ha).1,
    (Finset.mem_erase.mp hb).1, hab, hp, hlen⟩

/-- If a specified outside vertex has at most the named carrier neighbor,
the omitted boundary-root incidence forces a fresh dyadic ear avoiding that
outside vertex altogether.-/
theorem MinimalCounterexample.carrier_dyadic_ear_avoiding_unique_attachment
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V) (S : Set V)
    (hdisjoint : ∀ v, v ∈ K → v ∉ S)
    (hboundary : ∀ v, v ∈ K → ∀ w, w ∉ K → G.Adj v w → w ∈ S)
    (hsingle : ∀ v, v ∈ K → ∀ a, a ∉ K → ∀ b, b ∉ K →
      G.Adj v a → G.Adj v b → a = b)
    (hB : 4 ≤ (carrierBoundaryVertices G K).card)
    (hsize : 2 * K.card + 1 < Fintype.card V)
    (t : {v : V // v ∈ K}) (s : V) (hs : s ∈ S)
    (hunique : ∀ v, v ∈ K → G.Adj v s → v = t.1) :
    ∃ k : ℕ, ∃ a b : V, ∃ ear : G.Walk a b,
      2 ≤ k ∧ a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ear.IsPath ∧ ear.length = 2 ^ k ∧
      (∀ v, v ∈ ear.support → v = a ∨ v = b ∨ v ∈ K) ∧
      (∀ v, v ∈ ear.support → v ∈ S → v = a ∨ v = b) ∧
      s ∉ ear.support := by
  classical
  obtain ⟨k, a, b, q, hk, ha, hb, hat, hbt, hab, hq, hlen⟩ :=
    M.carrier_boundary_path_avoiding K hsingle hB hsize t
  obtain ⟨aOut, haOut, haa⟩ := (mem_carrierBoundaryVertices G K a).mp ha
  obtain ⟨bOut, hbOut, hbb⟩ := (mem_carrierBoundaryVertices G K b).mp hb
  have haS := hboundary a.1 a.2 aOut haOut haa
  have hbS := hboundary b.1 b.2 bOut hbOut hbb
  have haOutNe : aOut ≠ s := by
    intro h
    subst aOut
    exact hat (Subtype.ext (hunique a.1 a.2 haa))
  have hbOutNe : bOut ≠ s := by
    intro h
    subst bOut
    exact hbt (Subtype.ext (hunique b.1 b.2 hbb))
  let e : (G.induce (↑K : Set V)) ↪g G := SimpleGraph.Embedding.induce (↑K : Set V)
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
    exact M.isCounterexample.2 ⟨k, aOut, c, hk, hc, hclen.trans hplen⟩
  let ear : G.Walk aOut bOut := .cons haa.symm (p.concat hbb)
  have hear : ear.IsPath := by
    apply SimpleGraph.Walk.IsPath.cons (hp.concat hbavoid hbb)
    simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton]
    exact fun h => h.elim haavoid habOut
  have hsupport : ∀ v, v ∈ ear.support → v = aOut ∨ v = bOut ∨ v ∈ K := by
    intro v hv
    simp only [ear, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (hpK v h))
    · exact Or.inr (Or.inl h)
  refine ⟨k, aOut, bOut, ear, hk, haS, hbS, habOut, hear, ?_, hsupport, ?_, ?_⟩
  · simp only [ear, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat]
    omega
  · intro v hv hvS
    rcases hsupport v hv with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hdisjoint v h hvS).elim
  · intro h
    rcases hsupport s h with h | h | h
    · exact haOutNe h.symm
    · exact hbOutNe h.symm
    · exact hdisjoint s h hs

end Erdos64
