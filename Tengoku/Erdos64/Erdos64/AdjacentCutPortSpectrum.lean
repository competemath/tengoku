import Tengoku.Erdos64.Erdos64.AdjacentPortDoubleSuppression
import Tengoku.Erdos64.Erdos64.AdjacentTwoPortNonbipartite
import Tengoku.Erdos64.Erdos64.CutPortOddCycles

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Two suppressions of adjacent cubic ports supply an odd path one edge
longer than a power of two. The path stays in the original side.
@isnad1 id=ex.8h6v.s8.08a86bab9c50 from=translated src=- shape=df6f1a99 vocab=d5ab7036
-/
theorem MinimalCounterexample.exact_adjacent_cubic_side_pow_two_add_one_path
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hx : x ∈ D) (hy : y ∈ D)
    (hxy : G.Adj x y)
    (hboundary : ∀ a, a ∈ D → ∀ b, b ∉ D → G.Adj a b → b = r)
    (hexact : ∀ a, a ∈ D → (G.Adj a r ↔ a = x ∨ a = y))
    (hcubic : G.degree x = 3 ∧ G.degree y = 3) :
    ∃ k : ℕ, ∃ p : G.Walk x y,
      2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k + 1 ∧
      (∀ a, a ∈ p.support → a ∈ D) ∧ r ∉ p.support := by
  classical
  obtain ⟨hxdeg, hydeg, hretained, _⟩ :=
    two_cubic_ports_boundary_accounting D r x y hr ⟨hx, hy, hxy.ne⟩
      hboundary hexact hcubic
  let H := G.induce (↑D : Set V)
  let x' : (↑D : Set V) := ⟨x, hx⟩
  let y' : (↑D : Set V) := ⟨y, hy⟩
  have hx' : H.degree x' = 2 := by
    rw [degree_induce_coeFinset_eq_internalDegree]
    exact hxdeg
  have hy' : H.degree y' = 2 := by
    rw [degree_induce_coeFinset_eq_internalDegree]
    exact hydeg
  have hrx : G.Adj r x := ((hexact x hx).2 (Or.inl rfl)).symm
  have hry : G.Adj r y := ((hexact y hy).2 (Or.inr rfl)).symm
  have hcommon : ∀ z, H.Adj x' z → H.Adj y' z → False := by
    intro z hxz hyz
    have hxz' : G.Adj x z.1 := hxz
    have hyz' : G.Adj y z.1 := hyz
    have hzr := M.common_neighbor_eq_root_of_nonadjacent_ports hrx hry hxy.ne
      hxz' hyz' hxz'.ne.symm hyz'.ne.symm
    exact hr (hzr ▸ z.2)
  have hother : ∀ z, z ≠ x' → z ≠ y' → 3 ≤ H.degree z := by
    intro z hzx hzy
    rw [degree_induce_coeFinset_eq_internalDegree,
      hretained z.1 z.2 (fun h => hzx (Subtype.ext h))
        (fun h => hzy (Subtype.ext h))]
    exact degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 z.1
  have hno : ¬ HasPowerOfTwoCycle H :=
    not_hasPowerOfTwoCycle_induce_of_not_hasPowerOfTwoCycle M.isCounterexample.2
  have hsmall : Fintype.card (↑D : Set V) < Fintype.card V :=
    Fintype.card_subtype_lt (x := r) hr
  obtain ⟨k, q, hk, hq, hlen⟩ :=
    M.adjacent_degree_two_ports_pow_two_add_one_path
      x' y' hxy hx' hy' hcommon hother hno hsmall
  let e : H ↪g G := SimpleGraph.Embedding.induce (↑D : Set V)
  let p : G.Walk x y := q.map e.toHom
  have hinside : ∀ a, a ∈ p.support → a ∈ D := by
    intro a ha
    change a ∈ (q.map e.toHom).support at ha
    rw [SimpleGraph.Walk.support_map] at ha
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp ha
    exact z.2
  refine ⟨k, p, hk, hq.map e.injective, ?_, hinside, fun h => hr (hinside r h)⟩
  change (q.map e.toHom).length = 2 ^ k + 1
  rw [SimpleGraph.Walk.length_map]
  exact hlen

/-- Native adjacent attachments of a cut side carry a path of length
`2^k + 1`, in addition to the previously constructed even dyadic path.
@isnad1 id=ex.7h7v.s8.b8f9cd7f4063 from=translated src=- shape=469a9aa2 vocab=3412f5fb
-/
theorem EdgeMinimalCounterexample.rootDeleted_cut_adjacent_ports_pow_two_add_one_path
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : EdgeMinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hCD : C ≠ D) (x y : V)
    (hx : x ∈ rootDeletedComponentCarrier G r C)
    (hy : y ∈ rootDeletedComponentCarrier G r C)
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y) :
    ∃ k : ℕ, ∃ p : G.Walk x y,
      2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k + 1 ∧
      (∀ a, a ∈ p.support → a ∈ rootDeletedComponentCarrier G r C) ∧
      r ∉ p.support := by
  classical
  let := Fintype.ofFinite ((G.induce {v : V | v ≠ r}).ConnectedComponent)
  obtain ⟨_, _, hcard, _, _, hcubic⟩ :=
    M.rootDeleted_two_components_exact_balanced_cubic r C D hCD
  obtain ⟨a, b, ha, hb, hab, hra, hrb, hports⟩ :=
    rootDeletedComponent_twoPort_attachment_exact r C hcard
  have hxyports : ∀ z, z ∈ rootDeletedComponentCarrier G r C →
      G.Adj z r → z = x ∨ z = y := by
    rcases hports x hx hrx.symm with rfl | rfl <;>
      rcases hports y hy hry.symm with rfl | rfl
    · exact (hxy.ne rfl).elim
    · exact hports
    · intro z hz hzr
      exact (hports z hz hzr).symm
    · exact (hxy.ne rfl).elim
  have hexact : ∀ z, z ∈ rootDeletedComponentCarrier G r C →
      (G.Adj z r ↔ z = x ∨ z = y) := by
    intro z hz
    refine ⟨hxyports z hz, ?_⟩
    rintro (rfl | rfl)
    · exact hrx.symm
    · exact hry.symm
  have hboundary : ∀ a, a ∈ rootDeletedComponentCarrier G r C →
      ∀ b, b ∉ rootDeletedComponentCarrier G r C → G.Adj a b → b = r := by
    intro a ha b hb hab
    rcases (rootDeletedComponent_boundary r M.vertexMinimal.isConnected C).1
      a ha b hab with hbC | hbr
    · exact (hb hbC).elim
    · exact hbr
  exact M.vertexMinimal.exact_adjacent_cubic_side_pow_two_add_one_path
    (rootDeletedComponentCarrier G r C) r x y
    (rootDeletedComponentCarrier_nonempty_not_mem G r C).2 hx hy hxy
    hboundary hexact ⟨hcubic x hrx, hcubic y hry⟩

end Erdos64
