import Tengoku.Erdos64.Erdos64.GeneralBoundaryAvoidance
import Tengoku.Erdos64.Erdos64.CutSideDyadicEarAvoidance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Removing the synthetic root from a simple cycle based there leaves a
simple path between distinct boundary vertices, two edges shorter.
@isnad1 id=ex.1h4v.s6.73a1ee69b3a1 from=translated src=- shape=92c6b5d5 vocab=6d6f1bdc
-/
theorem boundaryRoot_root_cycle_path
    {W : Type u} {H : SimpleGraph W} {B : Finset W}
    (c : (boundaryRootGraph H B).Walk none none) (hc : c.IsCycle) :
    ∃ a b : W, ∃ p : H.Walk a b,
      a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ p.IsPath ∧ p.length + 2 = c.length := by
  classical
  let R := boundaryRootGraph H B
  cases c with
  | nil => exact (SimpleGraph.Walk.not_isCycle_nil hc).elim
  | @cons u v w h q =>
    have hqnotnil : ¬q.Nil := SimpleGraph.Walk.not_nil_of_isCycle_cons hc
    have hqpath : q.IsPath := by simpa using hc.isPath_tail
    have hdropnone : ∀ z, z ∈ q.dropLast.support → z ≠ none := by
      intro z hz hzn
      have hnodup : (q.dropLast.support ++ [none]).Nodup := by
        rw [q.support_dropLast_concat hqnotnil]
        exact hqpath.support_nodup
      exact (List.disjoint_left.mp (List.disjoint_of_nodup_append hnodup))
        hz (by simp [hzn])
    let S : Set (Option W) := {z | z ≠ none}
    let qi := q.dropLast.induce S hdropnone
    let e := boundaryRootDeletedIso H B
    let emb : R.induce S ↪g R := SimpleGraph.Embedding.induce S
    have hmap : qi.map emb.toHom = q.dropLast := q.dropLast.map_induce hdropnone
    have hqi : qi.IsPath := by
      apply (SimpleGraph.Walk.isPath_map_iff_of_injective
        (p := qi) (f := emb.toHom) emb.injective).mp
      rw [hmap]
      exact hqpath.dropLast
    let p := qi.map e.toHom
    have hp : p.IsPath := hqi.map e.injective
    have hplen : p.length = q.dropLast.length := by
      have hind := congrArg SimpleGraph.Walk.length hmap
      rw [SimpleGraph.Walk.length_map] at hind
      exact (SimpleGraph.Walk.length_map e.toHom qi).trans hind
    have hboundary : ∀ z : {z : Option W // z ≠ none},
        R.Adj none z.1 → e z ∈ B := by
      rintro ⟨z, hz⟩ hadj
      cases z with
      | none => exact (hz rfl).elim
      | some a => simpa [e, R] using hadj
    have ha := hboundary ⟨v, hdropnone v q.dropLast.start_mem_support⟩ h
    have hb := hboundary ⟨q.penultimate, hdropnone _ q.dropLast.end_mem_support⟩
      (q.adj_penultimate hqnotnil).symm
    have hlen : p.length + 2 = (SimpleGraph.Walk.cons h q).length := by
      rw [SimpleGraph.Walk.length_cons, ← q.length_dropLast_add_one hqnotnil]
      omega
    have hpositive : 0 < p.length := by
      have hthree := hc.three_le_length
      omega
    have hab : e ⟨v, hdropnone v q.dropLast.start_mem_support⟩ ≠
        e ⟨q.penultimate, hdropnone _ q.dropLast.end_mem_support⟩ := by
      intro heq
      exact (Nat.ne_of_gt hpositive) (hp.nil_iff_eq.mpr heq).length_eq_zero
    exact ⟨_, _, p, ha, hb, hab, hp, hlen⟩

/-- With a boundary root of degree at least two and at most one additional
degree-two defect, minimality forces a boundary path whose two-edge closure
has power-of-two length or one more than a power of two.
@isnad1 id=ex.6h6v.s8.c762576116d3 from=translated src=- shape=36ecdac5 vocab=899798c2
-/
theorem MinimalCounterexample.boundaryRoot_small_two_defect_path
    {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (M : MinimalCounterexample G) (B : Finset W) (t : W)
    (hB : 2 ≤ B.card)
    (ht : 2 ≤ (boundaryRootGraph H B).degree (some t))
    (hothers : ∀ w, w ≠ t → 3 ≤ (boundaryRootGraph H B).degree (some w))
    (hsize : 2 * Fintype.card W + 1 < Fintype.card V)
    (hno : ¬ HasPowerOfTwoCycle H) :
    ∃ k : ℕ, ∃ a b : W, ∃ p : H.Walk a b,
      1 ≤ k ∧ a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ p.IsPath ∧
      (p.length + 2 = 2 ^ k ∨ p.length + 2 = 2 ^ k + 1) := by
  classical
  let R := boundaryRootGraph H B
  by_cases hyes : HasPowerOfTwoCycle R
  · obtain ⟨k, a, b, p, hk, ha, hb, hab, hp, hlen⟩ :=
      boundaryRoot_dyadic_cycle_path B hno hyes
    exact ⟨k, a, b, p, by omega, ha, hb, hab, hp, Or.inl hlen⟩
  have hroot : R.degree none = 2 := by
    rw [boundaryRootGraph_degree_none]
    by_contra hne
    have hthree : 3 ≤ B.card := by omega
    have hrest : ∀ v, v ≠ some t → 3 ≤ R.degree v := by
      intro v hv
      cases v with
      | none =>
        change 3 ≤ (boundaryRootGraph H B).degree none
        rw [boundaryRootGraph_degree_none]
        exact hthree
      | some w => exact hothers w (fun h => hv (congrArg some h))
    have horder : 2 * Fintype.card (Option W) - 1 < Fintype.card V := by
      simp only [Fintype.card_option]
      omega
    exact hyes (M.one_defect_small_has_dyadic_cycle (some t) ht hrest horder)
  have hrest : ∀ v, v ≠ none → v ≠ some t → 3 ≤ R.degree v := by
    intro v hv0 hvt
    cases v with
    | none => exact (hv0 rfl).elim
    | some w => exact hothers w (fun h => hvt (congrArg some h))
  have horder : 2 * Fintype.card (Option W) - 3 < Fintype.card V := by
    simp only [Fintype.card_option]
    omega
  obtain ⟨k, c, hk, hc, hlen⟩ :=
    M.two_defect_port_dyadic_successor_cycle none (some t) (by simp)
      hroot ht hrest hyes horder
  obtain ⟨a, b, p, ha, hb, hab, hp, hplen⟩ := boundaryRoot_root_cycle_path c hc
  exact ⟨k, a, b, p, hk, ha, hb, hab, hp, Or.inr (hplen.trans hlen)⟩

/-- Three boundary vertices force a fresh ear avoiding a specified outside
vertex when every outside attachment has at most one carrier neighbor. Its
length is a power of two or one more than a power of two. Attachment
injectivity is essential for the odd branch to be a path rather than a cycle.
@isnad1 id=ex.7h5v.s8.717fd9fafb1b from=translated src=- shape=d65107fa vocab=b8771fe7
-/
theorem MinimalCounterexample.small_carrier_mixed_ear_avoiding_attachment
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V) (S : Set V)
    (hdisjoint : ∀ v, v ∈ K → v ∉ S)
    (hboundary : ∀ v, v ∈ K → ∀ w, w ∉ K → G.Adj v w → w ∈ S)
    (hB : 3 ≤ (carrierBoundaryVertices G K).card)
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
  have hK : K.Nonempty := by
    obtain ⟨v, _⟩ := Finset.card_pos.mp
      (show 0 < (carrierBoundaryVertices G K).card by omega)
    exact ⟨v.1, v.2⟩
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
  have hBtwo : 2 ≤ B.card := by
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

/-- In a component with at least three boundary vertices, a port path whose
vertices are all cubic admits a fresh avoiding ear with dyadic or dyadic-
successor length. Cubicity of every path vertex supplies injectivity of all
outside attachments, including the endpoints of the odd ear.
@isnad1 id=ex.10h10v.s9.3e18979a1cc0 from=translated src=- shape=f66c306e vocab=35dfc169
-/
theorem MinimalCounterexample.rootDeleted_cut_side_mixed_ear_avoiding_vertex_of_cubic_path
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y) (hp : p.IsPath)
    (hinside : ∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C)
    (E : (G.induce {v : V | v ∈ rootDeletedComponentCarrier G r C ∧
      v ∉ p.support}).ConnectedComponent)
    (hB : 3 ≤ (carrierBoundaryVertices G
      (offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E)).card)
    (hcubic : ∀ v, v ∈ p.support → G.degree v = 3)
    (s : V) (hs : s ∈ p.support) :
    ∃ k : ℕ, ∃ a b : V, ∃ ear : G.Walk a b,
      1 ≤ k ∧ a ∈ p.support ∧ b ∈ p.support ∧ a ≠ b ∧
      ear.IsPath ∧ (ear.length = 2 ^ k ∨ ear.length = 2 ^ k + 1) ∧
      (∀ v, v ∈ ear.support → v = a ∨ v = b ∨
        v ∈ offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E) ∧
      (∀ v, v ∈ ear.support → v ∈ p.support → v = a ∨ v = b) ∧
      s ∉ ear.support ∧
      (∀ v, v ∈ ear.support → v ∈ rootDeletedComponentCarrier G r C) := by
  classical
  let K := offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E
  obtain ⟨_, hKdata, hboundary, hsize⟩ :=
    cut_side_offPath_carrier_data M r C D hCD hxy hrx hry p hinside E
  have hattachments : ∀ w, w ∈ p.support → ∀ a, a ∈ K → ∀ b, b ∈ K →
      G.Adj a w → G.Adj b w → a = b := by
    intro w hw a ha b hb haw hbw
    exact cut_side_port_path_external_neighbors_eq r C hxy hrx hry p hp hinside
      K hKdata w hw (hcubic w hw) a ha b hb haw.symm hbw.symm
  obtain ⟨k, a, b, ear, hk, ha, hb, hab, hear, hlen, hsupport, hfresh, hsavoid⟩ :=
    M.small_carrier_mixed_ear_avoiding_attachment K {v | v ∈ p.support}
      (fun v hv => (hKdata v hv).2) hboundary hB hsize hattachments s hs
  refine ⟨k, a, b, ear, hk, ha, hb, hab, hear, hlen, hsupport, hfresh, hsavoid, ?_⟩
  intro v hv
  rcases hsupport v hv with hva | hvb | hvK
  · subst v
    exact hinside a ha
  · subst v
    exact hinside b hb
  · exact (hKdata v hvK).1

end Erdos64
