import Tengoku.Erdos64.Erdos64.ThreeBoundaryAvoidance
import Tengoku.Seed.Algebra.BigOperators.Ring.Nat
import Tengoku.Seed.Combinatorics.SimpleGraph.DegreeSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- For odd order and odd original degrees, restoring one lost incidence
forces an even number of boundary incidences.-/
private theorem boundary_card_even_of_odd_degrees_after_one_loss
    {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (B : Finset W) (t : W)
    (hodd : Odd (Fintype.card W))
    (hdegrees : ∀ v, Odd (H.degree v + (if v ∈ B then 1 else 0) +
      (if v = t then 1 else 0))) : Even B.card := by
  classical
  have hfilter : Finset.univ.filter (fun v => Odd (H.degree v +
      (if v ∈ B then 1 else 0) + (if v = t then 1 else 0))) = Finset.univ := by
    ext v
    simp [hdegrees]
  have hsumodd : Odd (∑ v, (H.degree v + (if v ∈ B then 1 else 0) +
      (if v = t then 1 else 0))) := by
    apply (Finset.odd_sum_iff_odd_card_odd _).mpr
    simpa only [hfilter, Finset.card_univ] using hodd
  have hsumB : (∑ v : W, if v ∈ B then 1 else 0) = B.card := by
    simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumB,
    Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ t),
    H.sum_degrees_eq_twice_card_edges] at hsumodd
  obtain ⟨k, hk⟩ := hsumodd
  exact ⟨k - H.edgeFinset.card, by omega⟩

/-- An odd-order carrier whose ambient degrees are all odd admits a fresh
ear avoiding any specified outside vertex, provided outside attachments
are injective and the carrier is sufficiently small. The ear length is a
power of two or one more than a power of two.-/
theorem MinimalCounterexample.odd_carrier_mixed_ear_avoiding_attachment
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V) (S : Set V)
    (hdisjoint : ∀ v, v ∈ K → v ∉ S)
    (hboundary : ∀ v, v ∈ K → ∀ w, w ∉ K → G.Adj v w → w ∈ S)
    (hKodd : Odd K.card)
    (hodddegrees : ∀ v, v ∈ K → Odd (G.degree v))
    (hsize : 2 * K.card + 1 < Fintype.card V)
    (hattachments : ∀ w, w ∈ S → ∀ a, a ∈ K → ∀ b, b ∈ K →
      G.Adj a w → G.Adj b w → a = b)
    (s : V) (hs : s ∈ S) :
    ∃ k : ℕ, ∃ a b : V, ∃ ear : G.Walk a b,
      1 ≤ k ∧ a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ear.IsPath ∧ (ear.length = 2 ^ k ∨ ear.length = 2 ^ k + 1) ∧
      (∀ v, v ∈ ear.support → v = a ∨ v = b ∨ v ∈ K) ∧
      (∀ v, v ∈ ear.support → v ∈ S → v = a ∨ v = b) ∧
      s ∉ ear.support := by
  classical
  have hK : K.Nonempty := Finset.card_pos.mp hKodd.pos
  obtain ⟨t, hunique⟩ : ∃ t : {v : V // v ∈ K},
      ∀ v, v ∈ K → G.Adj v s → v = t.1 := by
    by_cases hattach : ∃ t, t ∈ K ∧ G.Adj t s
    · obtain ⟨t, ht, hts⟩ := hattach
      exact ⟨⟨t, ht⟩, fun v hv hvs => hattachments s hs v hv t ht hvs hts⟩
    · obtain ⟨t, ht⟩ := hK
      exact ⟨⟨t, ht⟩, fun v hv hvs => (hattach ⟨v, hv, hvs⟩).elim⟩
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
      hboundary v hv b hbK hvb', hab, hear, Or.inl rfl, hsupport, ?_, ?_⟩
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
  let H := L.induce (↑K : Set V)
  let R := boundaryRootGraph H B
  have hdegree : ∀ v, R.degree (some v) = L.degree v.1 := by
    intro v
    rw [boundaryRootGraph_degree_some]
    exact carrier_degree_add_boundary_indicator K hsingle v
  have htroot : 2 ≤ R.degree (some t) := by
    rw [hdegree]
    exact htdegree
  have hrest : ∀ v, v ≠ t → 3 ≤ R.degree (some v) := by
    intro v hv
    rw [hdegree]
    exact hothers v.1 v.2 (fun h => hv (Subtype.ext h))
  have horder : 2 * Fintype.card (↑K : Set V) + 1 < Fintype.card V := by
    simpa using hsize
  let e : H →g G :=
    { toFun := Subtype.val
      map_rel' := fun h => hle h }
  have hno : ¬ HasPowerOfTwoCycle H := by
    rintro ⟨k, v, c, hk, hc, hlen⟩
    exact M.isCounterexample.2 ⟨k, e v, c.map e, hk,
      hc.map Subtype.val_injective, by simpa using hlen⟩
  have hBtwo : 2 ≤ B.card := by
    by_cases hts : G.Adj t.1 s
    · have hdeleted : ∀ v : (↑K : Set V),
          L.degree v.1 + (if v = t then 1 else 0) = G.degree v.1 := by
        intro v
        by_cases hvt : v = t
        · subst v
          have hst : s ∈ G.neighborFinset t.1 :=
            (G.mem_neighborFinset t.1 s).mpr hts
          simp only [↓reduceIte]
          rw [← SimpleGraph.card_neighborFinset_eq_degree,
            hneighbors t.1 t.2]
          exact Finset.card_erase_add_one hst
        · have hnot : s ∉ G.neighborFinset v.1 := by
            intro h
            exact hvt (Subtype.ext (hunique v.1 v.2
              ((G.mem_neighborFinset v.1 s).mp h)))
          simp only [hvt, ↓reduceIte, Nat.add_zero]
          rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbors v.1 v.2,
            Finset.erase_eq_of_notMem hnot, SimpleGraph.card_neighborFinset_eq_degree]
      have hparity : Even B.card := by
        apply boundary_card_even_of_odd_degrees_after_one_loss H B t
          (by simpa using hKodd)
        intro v
        have hdeg := carrier_degree_add_boundary_indicator K hsingle v
        have hdel := hdeleted v
        have heq : H.degree v + (if v ∈ B then 1 else 0) +
            (if v = t then 1 else 0) = G.degree v.1 := by
          change H.degree v + (if v ∈ B then 1 else 0) = L.degree v.1 at hdeg
          omega
        rw [heq]
        exact hodddegrees v.1 v.2
      have hnonempty : 0 < B.card := by
        by_contra hzero
        have hBempty : B = ∅ := Finset.card_eq_zero.mp (by omega)
        have hdeg : ∀ v, H.degree v = L.degree v.1 := by
          intro v
          have h := carrier_degree_add_boundary_indicator K hsingle v
          change H.degree v + (if v ∈ B then 1 else 0) = L.degree v.1 at h
          simpa only [hBempty, Finset.notMem_empty, ↓reduceIte, Nat.add_zero] using h
        apply hno
        apply M.one_defect_small_has_dyadic_cycle t
        · rw [hdeg]
          exact htdegree
        · intro v hv
          rw [hdeg]
          exact hothers v.1 v.2 (fun h => hv (Subtype.ext h))
        · simpa using (show 2 * K.card - 1 < Fintype.card V by omega)
      obtain ⟨j, hj⟩ := hparity
      omega
    · have hnot : ∀ v, v ∈ K → ¬G.Adj v s := by
        intro v hv hvs
        have heq := hunique v hv hvs
        exact hts (heq ▸ hvs)
      have hsingleG : ∀ v, v ∈ K → ∀ a, a ∉ K → ∀ b, b ∉ K →
          G.Adj v a → G.Adj v b → a = b := by
        intro v hv a ha b hb hva hvb
        have has : a ≠ s := fun h => hnot v hv (h ▸ hva)
        have hbs : b ≠ s := fun h => hnot v hv (h ▸ hvb)
        exact hsingle v hv a ha b hb
          (hLadj.mpr ⟨hva, hne v hv, has⟩) (hLadj.mpr ⟨hvb, hne v hv, hbs⟩)
      have hBeq : B = carrierBoundaryVertices G K := by
        ext v
        simp only [B, mem_carrierBoundaryVertices]
        constructor
        · rintro ⟨w, hw, hvw⟩
          exact ⟨w, hw, hle hvw⟩
        · rintro ⟨w, hw, hvw⟩
          have hws : w ≠ s := fun h => hnot v.1 v.2 (h ▸ hvw)
          exact ⟨w, hw, hLadj.mpr ⟨hvw, hne v.1 v.2, hws⟩⟩
      rw [hBeq]
      exact M.small_carrier_boundary_card_ge_two K hK hsingleG hsize
  obtain ⟨k, a, b, q, hk, ha, hb, hab, hq, hlen⟩ :=
    M.boundaryRoot_small_two_defect_path B t hBtwo htroot hrest horder hno
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
  have hplen : p.length + 2 = 2 ^ k ∨ p.length + 2 = 2 ^ k + 1 := by
    change (q.map e).length + 2 = 2 ^ k ∨ (q.map e).length + 2 = 2 ^ k + 1
    rw [SimpleGraph.Walk.length_map]
    exact hlen
  have haavoid : aOut ∉ p.support := fun h => haOut (hpK aOut h)
  have hbavoid : bOut ∉ p.support := fun h => hbOut (hpK bOut h)
  have habOut : aOut ≠ bOut := by
    intro heq
    subst bOut
    exact hab (Subtype.ext (hattachments aOut haS a.1 a.2 b.1 b.2 haa hbb))
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
    rcases hplen with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
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
