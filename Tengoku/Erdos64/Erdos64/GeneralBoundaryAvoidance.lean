import Tengoku.Erdos64.Erdos64.SmallCarrierDyadicEar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Four boundary vertices allow a fresh dyadic ear avoiding an outside
vertex with at most one carrier neighbor. No bound on the other external
incidences of carrier vertices is needed: two permitted external neighbors
already give a two-edge ear.
@isnad1 id=ex.7h6v.s8.dd0906db3f42 from=translated src=- shape=05b2d139 vocab=7a53d3f1
-/
theorem MinimalCounterexample.small_carrier_dyadic_ear_avoiding_unique_attachment
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V) (S : Set V)
    (hdisjoint : ∀ v, v ∈ K → v ∉ S)
    (hboundary : ∀ v, v ∈ K → ∀ w, w ∉ K → G.Adj v w → w ∈ S)
    (hB : 4 ≤ (carrierBoundaryVertices G K).card)
    (hsize : 2 * K.card + 1 < Fintype.card V)
    (t : {v : V // v ∈ K}) (s : V) (hs : s ∈ S)
    (hunique : ∀ v, v ∈ K → G.Adj v s → v = t.1) :
    ∃ k : ℕ, ∃ a b : V, ∃ ear : G.Walk a b,
      1 ≤ k ∧ a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ear.IsPath ∧ ear.length = 2 ^ k ∧
      (∀ v, v ∈ ear.support → v = a ∨ v = b ∨ v ∈ K) ∧
      (∀ v, v ∈ ear.support → v ∈ S → v = a ∨ v = b) ∧
      s ∉ ear.support := by
  classical
  have hsK : s ∉ K := fun h => hdisjoint s h hs
  have hne : ∀ v, v ∈ K → v ≠ s := by
    intro v hv hvs
    exact hsK (hvs ▸ hv)
  let L := G.deleteIncidenceSet s
  have hLadj : ∀ {v w}, L.Adj v w ↔ G.Adj v w ∧ v ≠ s ∧ w ≠ s :=
    fun {_ _} => SimpleGraph.deleteIncidenceSet_adj
  have hle : L ≤ G := G.deleteIncidenceSet_le s
  by_cases htwo : ∃ v ∈ K, ∃ a, a ∉ K ∧ ∃ b, b ∉ K ∧
      a ≠ b ∧ L.Adj v a ∧ L.Adj v b
  · obtain ⟨v, hv, a, haK, b, hbK, hab, hva, hvb⟩ := htwo
    have hva' := (hLadj.mp hva).1
    have hvb' := (hLadj.mp hvb).1
    let ear : G.Walk a b := .cons hva'.symm (.cons hvb' .nil)
    have hear : ear.IsPath := by
      apply SimpleGraph.Walk.IsPath.cons
      · exact SimpleGraph.Walk.IsPath.of_adj hvb'
      · simp [hva'.ne.symm, hab]
    have hsupport : ∀ w, w ∈ ear.support → w = a ∨ w = b ∨ w ∈ K := by
      intro w hw
      simp only [ear, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hv)
      · exact Or.inr (Or.inl rfl)
    refine ⟨1, a, b, ear, by omega, hboundary v hv a haK hva',
      hboundary v hv b hbK hvb', hab, hear, rfl, hsupport, ?_, ?_⟩
    · intro w hw hwS
      rcases hsupport w hw with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hdisjoint w h hwS).elim
    · intro h
      rcases hsupport s h with h | h | h
      · exact (hLadj.mp hva).2.2 h.symm
      · exact (hLadj.mp hvb).2.2 h.symm
      · exact hsK h
  have hsingle : ∀ v, v ∈ K → ∀ a, a ∉ K → ∀ b, b ∉ K →
      L.Adj v a → L.Adj v b → a = b := by
    intro v hv a ha b hb hva hvb
    by_contra hab
    exact htwo ⟨v, hv, a, ha, b, hb, hab, hva, hvb⟩
  have hneighbors : ∀ v, v ∈ K →
      L.neighborFinset v = (G.neighborFinset v).erase s := by
    intro v hv
    ext w
    simp [SimpleGraph.mem_neighborFinset, hLadj, hne v hv, and_comm]
  have htdegree : 2 ≤ L.degree t.1 := by
    have hmin := degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 t.1
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbors t.1 t.2]
    by_cases hst : s ∈ G.neighborFinset t.1
    · rw [Finset.card_erase_of_mem hst, SimpleGraph.card_neighborFinset_eq_degree]
      omega
    · rw [Finset.erase_eq_of_notMem hst, SimpleGraph.card_neighborFinset_eq_degree]
      omega
  have hothers : ∀ v, v ∈ K → v ≠ t.1 → 3 ≤ L.degree v := by
    intro v hv hvt
    have hnot : s ∉ G.neighborFinset v := by
      intro h
      exact hvt (hunique v hv ((G.mem_neighborFinset v s).mp h))
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbors v hv,
      Finset.erase_eq_of_notMem hnot, SimpleGraph.card_neighborFinset_eq_degree]
    exact degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 v
  let B := carrierBoundaryVertices L K
  have hBsub : (carrierBoundaryVertices G K).erase t ⊆ B := by
    intro v hv
    obtain ⟨hvt, hvB⟩ := Finset.mem_erase.mp hv
    obtain ⟨w, hwK, hvw⟩ := (mem_carrierBoundaryVertices G K v).mp hvB
    have hws : w ≠ s := by
      intro h
      subst w
      exact hvt (Subtype.ext (hunique v.1 v.2 hvw))
    exact (mem_carrierBoundaryVertices L K v).mpr
      ⟨w, hwK, hLadj.mpr ⟨hvw, hne v.1 v.2, hws⟩⟩
  have hBthree : 3 ≤ B.card := by
    have hc := Finset.card_le_card hBsub
    by_cases htB : t ∈ carrierBoundaryVertices G K
    · rw [Finset.card_erase_of_mem htB] at hc
      omega
    · rw [Finset.erase_eq_of_notMem htB] at hc
      omega
  let H := L.induce (↑K : Set V)
  let R := boundaryRootGraph H B
  have hdegree : ∀ v, R.degree (some v) = L.degree v.1 := by
    intro v
    rw [boundaryRootGraph_degree_some]
    exact carrier_degree_add_boundary_indicator K hsingle v
  have htroot : 2 ≤ R.degree (some t) := by
    rw [hdegree]
    exact htdegree
  have hrest : ∀ v, v ≠ some t → 3 ≤ R.degree v := by
    intro v hv
    cases v with
    | none =>
      rw [boundaryRootGraph_degree_none]
      exact hBthree
    | some v =>
      rw [hdegree]
      exact hothers v.1 v.2 (fun h => hv (congrArg some (Subtype.ext h)))
  have horder : 2 * Fintype.card (Option (↑K : Set V)) - 1 < Fintype.card V := by
    simpa using (show 2 * (K.card + 1) - 1 < Fintype.card V by omega)
  have hyes := M.one_defect_small_has_dyadic_cycle (some t) htroot hrest horder
  let e : H →g G :=
    { toFun := Subtype.val
      map_rel' := fun h => hle h }
  have hno : ¬ HasPowerOfTwoCycle H := by
    rintro ⟨k, v, c, hk, hc, hlen⟩
    exact M.isCounterexample.2 ⟨k, e v, c.map e, hk,
      hc.map Subtype.val_injective, by simpa using hlen⟩
  obtain ⟨k, a, b, q, hk, ha, hb, hab, hq, hlen⟩ :=
    boundaryRoot_dyadic_cycle_path B hno hyes
  obtain ⟨aOut, haOut, haaL⟩ := (mem_carrierBoundaryVertices L K a).mp ha
  obtain ⟨bOut, hbOut, hbbL⟩ := (mem_carrierBoundaryVertices L K b).mp hb
  have haa := hle haaL
  have hbb := hle hbbL
  have haS := hboundary a.1 a.2 aOut haOut haa
  have hbS := hboundary b.1 b.2 bOut hbOut hbb
  let p : G.Walk a.1 b.1 := q.map e
  have hp : p.IsPath := hq.map Subtype.val_injective
  have hpK : ∀ v, v ∈ p.support → v ∈ K := by
    intro v hv
    change v ∈ (q.map e).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
    exact w.2
  have hplen : p.length + 2 = 2 ^ k := by
    change (q.map e).length + 2 = 2 ^ k
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
  refine ⟨k, aOut, bOut, ear, by omega, haS, hbS, habOut, hear, ?_, hsupport, ?_, ?_⟩
  · simp only [ear, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat]
    omega
  · intro v hv hvS
    rcases hsupport v hv with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hdisjoint v h hvS).elim
  · intro h
    rcases hsupport s h with h | h | h
    · exact (hLadj.mp haaL).2.2 h.symm
    · exact (hLadj.mp hbbL).2.2 h.symm
    · exact hsK h

end Erdos64
