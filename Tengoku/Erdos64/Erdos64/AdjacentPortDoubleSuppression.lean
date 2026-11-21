import Tengoku.Erdos64.Erdos64.DegreeTwoSuppression
import Tengoku.Erdos64.Erdos64.AddedEdgeCyclePath

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

private theorem degree_two_neighbor_description
    {W : Type u} {H : SimpleGraph W}
    [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    {x y : W} (hxy : H.Adj x y) (hx : H.degree x = 2) :
    ∃ u, u ≠ y ∧ ∀ w, H.Adj x w ↔ w = y ∨ w = u := by
  classical
  have hy : y ∈ H.neighborFinset x := by simpa using hxy
  have hcard : (H.neighborFinset x).card = 2 := by simpa using hx
  have hpos : 0 < ((H.neighborFinset x).erase y).card := by
    rw [Finset.card_erase_of_mem hy, hcard]
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  obtain ⟨huy, hu⟩ := Finset.mem_erase.mp hu
  have hsub : ({y, u} : Finset W) ⊆ H.neighborFinset x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hy
    · exact hu
  have heq : ({y, u} : Finset W) = H.neighborFinset x :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hcard, huy.symm])
  refine ⟨u, huy, ?_⟩
  intro w
  rw [← SimpleGraph.mem_neighborFinset, ← heq]
  simp

/-- Suppressing two adjacent degree-two terminals repairs all degrees. A
dyadic cycle in the smaller suppressed graph supplies a terminal path one
edge longer than a power of two in the original graph.
@isnad1 id=ex.10h8v.s7.ff872fc995a2 from=translated src=- shape=5442b353 vocab=ebf90c69
-/
theorem MinimalCounterexample.adjacent_two_defect_pow_two_add_one_path
    {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (M : MinimalCounterexample G) (x y u v : W)
    (huy : u ≠ y) (hvx : v ≠ x) (huv : u ≠ v)
    (hnadj : ¬H.Adj u v)
    (hnx : ∀ w, H.Adj x w ↔ w = y ∨ w = u)
    (hny : ∀ w, H.Adj y w ↔ w = x ∨ w = v)
    (hother : ∀ w, w ≠ x → w ≠ y → 3 ≤ H.degree w)
    (hno : ¬HasPowerOfTwoCycle H)
    (hsize : Fintype.card W < Fintype.card V) :
    ∃ k : ℕ, ∃ p : H.Walk x y,
      2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k + 1 := by
  classical
  have hxy : H.Adj x y := (hnx y).2 (Or.inl rfl)
  have hxu : H.Adj x u := (hnx u).2 (Or.inr rfl)
  have hyv : H.Adj y v := (hny v).2 (Or.inr rfl)
  have hyu : ¬H.Adj y u := by
    intro h
    rcases (hny u).1 h with h | h
    · exact hxu.ne h.symm
    · exact huv h
  let X := {w : W // w ≠ x}
  let yy : X := ⟨y, hxy.ne.symm⟩
  let uu : X := ⟨u, hxu.ne.symm⟩
  let vv : X := ⟨v, hvx⟩
  let K := degreeTwoSuppressionGraph H x y u hxy.ne.symm hxu.ne.symm
  have huuyy : uu ≠ yy := fun h => huy (congrArg Subtype.val h)
  have hvvyy : vv ≠ yy := fun h => hyv.ne (congrArg Subtype.val h).symm
  have huuvv : uu ≠ vv := fun h => huv (congrArg Subtype.val h)
  have hKdeg : ∀ w : X, K.degree w = H.degree w.1 := by
    intro w
    exact degreeTwoSuppressionGraph_degree H x y u hxy.ne.symm
      hxu.ne.symm huy.symm hyu hnx w
  have hKneighbors : ∀ w : X, K.Adj yy w ↔ w = uu ∨ w = vv := by
    intro w
    change (H.Adj y w.1 ∨ (SimpleGraph.edge yy uu).Adj yy w) ↔ _
    rw [hny]
    have hwx : w.1 ≠ x := w.2
    simp only [SimpleGraph.edge_adj, true_and, hwx, false_or]
    simp only [X, yy, uu, vv, Subtype.ext_iff] at *
    aesop
  have hKnadj : ¬K.Adj uu vv := by
    change ¬(H.Adj u v ∨ (SimpleGraph.edge yy uu).Adj uu vv)
    simp only [SimpleGraph.edge_adj]
    simp [hnadj, huuyy, hvvyy]
  let T := {w : X // w ≠ yy}
  let a : T := ⟨uu, huuyy⟩
  let b : T := ⟨vv, hvvyy⟩
  let A : SimpleGraph T := H.comap (fun w => w.1.1)
  let L := degreeTwoSuppressionGraph K yy uu vv huuyy hvvyy
  have hLdegree : ∀ w : T, L.degree w = H.degree w.1.1 := by
    intro w
    rw [show L.degree w = K.degree w.1 from
      degreeTwoSuppressionGraph_degree K yy uu vv huuyy hvvyy
        huuvv hKnadj hKneighbors w, hKdeg]
  have hLdef : L = A ⊔ SimpleGraph.edge a b := by
    ext s t
    change ((H.Adj s.1.1 t.1.1 ∨ (SimpleGraph.edge yy uu).Adj s.1 t.1) ∨
      (SimpleGraph.edge a b).Adj s t) ↔ _
    have hs : s.1 ≠ yy := s.2
    have ht : t.1 ≠ yy := t.2
    simp only [SimpleGraph.sup_adj, A, SimpleGraph.comap_adj,
      SimpleGraph.edge_adj, hs, ht, false_and, and_false, or_false]
  let e : A ↪g H :=
    { toFun := fun w => w.1.1
      inj' := fun s t h => Subtype.ext (Subtype.ext h)
      map_rel_iff' := Iff.rfl }
  have hAno : ¬HasPowerOfTwoCycle A := by
    rintro ⟨k, z, c, hk, hc, hlen⟩
    apply hno
    exact ⟨k, e z, c.map e.toHom, hk, hc.map e.injective,
      by simpa using hlen⟩
  have hLyes : HasPowerOfTwoCycle L := by
    by_contra hLno
    have hLmin : 3 ≤ L.minDegree := by
      let : Nonempty T := ⟨a⟩
      apply L.le_minDegree_of_forall_le_degree
      intro w
      rw [hLdegree]
      exact hother w.1.1 w.1.2 (fun h => w.2 (Subtype.ext h))
    have hcard : Fintype.card T < Fintype.card V := by
      exact lt_of_le_of_lt
        (le_trans (Fintype.card_subtype_le _) (Fintype.card_subtype_le _)) hsize
    exact M.not_exists_strictly_smaller (H := L) ⟨⟨hLmin, hLno⟩, hcard⟩
  rw [hLdef] at hLyes
  obtain ⟨k, p, hk, hp, hlen⟩ := added_edge_dyadic_cycle_path hAno hLyes
  let q : H.Walk u v := p.map e.toHom
  have hq : q.IsPath := hp.map e.injective
  have havoid : ∀ w, w ∈ q.support → w ≠ x ∧ w ≠ y := by
    intro w hw
    change w ∈ (p.map e.toHom).support at hw
    rw [SimpleGraph.Walk.support_map] at hw
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hw
    exact ⟨t.1.2, fun h => t.2 (Subtype.ext h)⟩
  let result : H.Walk x y := (q.cons hxu).concat hyv.symm
  have hresult : result.IsPath := by
    apply SimpleGraph.Walk.IsPath.concat
    · exact hq.cons (fun hx => (havoid x hx).1 rfl)
    · simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      rintro (h | h)
      · exact hxy.ne h.symm
      · exact (havoid y h).2 rfl
  refine ⟨k, result, hk, hresult, ?_⟩
  have hqlen : q.length + 1 = 2 ^ k := by
    simpa [q] using hlen
  simp only [result, SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_cons]
  omega

/-- Degree-two adjacent terminals with no common neighbor force a path one
edge beyond a dyadic length. The no-common-neighbor condition rules out the
isolated-triangle obstruction and lets both suppressions preserve degrees.
@isnad1 id=ex.8h6v.s8.f50c7bd82a51 from=translated src=- shape=61fc1628 vocab=ebf90c69
-/
theorem MinimalCounterexample.adjacent_degree_two_ports_pow_two_add_one_path
    {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (M : MinimalCounterexample G) (x y : W)
    (hxy : H.Adj x y) (hxdeg : H.degree x = 2) (hydeg : H.degree y = 2)
    (hcommon : ∀ z, H.Adj x z → H.Adj y z → False)
    (hother : ∀ w, w ≠ x → w ≠ y → 3 ≤ H.degree w)
    (hno : ¬HasPowerOfTwoCycle H)
    (hsize : Fintype.card W < Fintype.card V) :
    ∃ k : ℕ, ∃ p : H.Walk x y,
      2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k + 1 := by
  obtain ⟨u, huy, hnx⟩ := degree_two_neighbor_description hxy hxdeg
  obtain ⟨v, hvx, hny⟩ := degree_two_neighbor_description hxy.symm hydeg
  have hxu : H.Adj x u := (hnx u).2 (Or.inr rfl)
  have hyv : H.Adj y v := (hny v).2 (Or.inr rfl)
  have huv : u ≠ v := by
    intro h
    exact hcommon u hxu (h ▸ hyv)
  have hnadj : ¬H.Adj u v := by
    intro huvAdj
    let q : H.Walk u y := huvAdj.toWalk.append hyv.symm.toWalk
    have hq : q.IsPath := by
      change (SimpleGraph.Walk.cons huvAdj
        (SimpleGraph.Walk.cons hyv.symm SimpleGraph.Walk.nil)).IsPath
      simp only [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false]
      exact ⟨⟨SimpleGraph.Walk.IsPath.nil, hyv.ne.symm⟩,
        fun h => h.elim huv huy⟩
    have hxnot : x ∉ q.support := by
      simp [q, hxu.ne, hvx.symm, hxy.ne]
    obtain ⟨c, hc, hlen⟩ := endpoint_fan_cycle_certificate
      hq hxu hxy hxnot huy (by simp [q])
    apply hno
    exact ⟨2, u, c, by omega, hc, by simpa [q] using hlen⟩
  exact M.adjacent_two_defect_pow_two_add_one_path x y u v
    huy hvx huv hnadj hnx hny hother hno hsize

end Erdos64
