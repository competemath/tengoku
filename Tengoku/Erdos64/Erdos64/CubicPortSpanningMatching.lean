import Tengoku.Erdos64.Erdos64.SpanningPathMatching
import Tengoku.Erdos64.Erdos64.CutSidePathParity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

open scoped Classical

/-- The precise matching reduction for a cubic carrier with two root ports.
The induced path maps back to the supplied ambient path, and its complement
is a perfect matching. The spanning path is necessarily odd.
@isnad1 id=and.10h7v.s10.103e09c9ce12 from=translated src=- shape=22f987cc vocab=4dbd5e3e
-/
theorem exact_two_port_spanning_path_matching
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D : Finset V) (r x y : V) (hr : r ∉ D)
    (hx : x ∈ D) (hy : y ∈ D) (hxy : x ≠ y)
    (hboundary : ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hexact : ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (hcubic : ∀ v, v ∈ D → G.degree v = 3)
    (p : G.Walk x y) (hp : p.IsPath)
    (hinside : ∀ v, v ∈ p.support → v ∈ D)
    (hspan : ∀ v, v ∈ D → v ∈ p.support) :
    Odd p.length ∧
      ∃ q : (G.induce (↑D : Set V)).Walk ⟨x, hx⟩ ⟨y, hy⟩,
        q.map (SimpleGraph.Embedding.induce (↑D : Set V)).toHom = p ∧
        q.IsPath ∧ (∀ v, v ∈ q.support) ∧
        ((G.induce (↑D : Set V)).toSubgraph
          ((G.induce (↑D : Set V)) \ q.toSubgraph.spanningCoe) sdiff_le).IsPerfectMatching := by
  classical
  let H := G.induce (↑D : Set V)
  let q : H.Walk ⟨x, hx⟩ ⟨y, hy⟩ := p.induce (↑D : Set V) hinside
  let e : H ↪g G := SimpleGraph.Embedding.induce (↑D : Set V)
  have hmap : q.map e.toHom = p := SimpleGraph.Walk.map_induce p hinside
  have hq : q.IsPath := by
    apply (SimpleGraph.Walk.isPath_map_iff_of_injective (f := e.toHom) e.injective).mp
    rwa [hmap]
  have hqspan : ∀ v, v ∈ q.support := by
    intro v
    have hv : v.1 ∈ (q.map e.toHom).support := by
      rw [hmap]
      exact hspan v.1 v.2
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨w, hw, heq⟩ := List.mem_map.mp hv
    have hweq : w = v := e.injective heq
    exact hweq ▸ hw
  have hqdeg : ∀ v : (↑D : Set V),
      H.degree v = if v = ⟨x, hx⟩ ∨ v = ⟨y, hy⟩ then 2 else 3 := by
    intro v
    have haccount := internalDegree_add_root_indicator_eq_degree D r hr hboundary v.2
    rw [hcubic v.1 v.2] at haccount
    rw [degree_induce_coeFinset_eq_internalDegree]
    by_cases hv : v = (⟨x, hx⟩ : (↑D : Set V)) ∨ v = ⟨y, hy⟩
    · have hroot : G.Adj v.1 r := (hexact v.1 v.2).mpr
        (hv.elim (fun h => Or.inl (congrArg Subtype.val h))
          (fun h => Or.inr (congrArg Subtype.val h)))
      simp only [hroot, ↓reduceIte] at haccount
      rw [ite_eq_left hv]
      omega
    · have hroot : ¬G.Adj v.1 r := by
        intro h
        apply hv
        exact ((hexact v.1 v.2).mp h).elim
          (fun h => Or.inl (Subtype.ext h)) (fun h => Or.inr (Subtype.ext h))
      simp only [hroot, ↓reduceIte, Nat.add_zero] at haccount
      simpa only [ite_eq_right hv] using haccount
  have hne : (⟨x, hx⟩ : (↑D : Set V)) ≠ ⟨y, hy⟩ :=
    fun h => hxy (congrArg Subtype.val h)
  have hodd := spanning_two_port_path_length_odd q hq hne hqspan hqdeg
  have hlen : q.length = p.length := by
    have h := congrArg (fun w : G.Walk x y => w.length) hmap
    exact (SimpleGraph.Walk.length_map e.toHom q).symm.trans h
  refine ⟨hlen ▸ hodd, q, hmap, hq, hqspan, ?_⟩
  exact spanning_two_port_path_complement_isPerfectMatching q hq hne hqspan hqdeg

/-- Native specialization of the spanning matching reduction to a cubic
side of a minimal counterexample with a cut root.
@isnad1 id=and.9h8v.s10.315c4bc9dd30 from=translated src=- shape=f5bae789 vocab=c0898db5
-/
theorem MinimalCounterexample.rootDeleted_spanning_cubic_path_matching
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y) (hp : p.IsPath)
    (hinside : ∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C)
    (hspan : ∀ v, v ∈ rootDeletedComponentCarrier G r C → v ∈ p.support)
    (hcubic : ∀ v, v ∈ rootDeletedComponentCarrier G r C → G.degree v = 3) :
    Odd p.length ∧
      ∃ q : (G.induce (↑(rootDeletedComponentCarrier G r C) : Set V)).Walk
          ⟨x, hinside x p.start_mem_support⟩ ⟨y, hinside y p.end_mem_support⟩,
        q.map (SimpleGraph.Embedding.induce
          (↑(rootDeletedComponentCarrier G r C) : Set V)).toHom = p ∧
        q.IsPath ∧ (∀ v, v ∈ q.support) ∧
        ((G.induce (↑(rootDeletedComponentCarrier G r C) : Set V)).toSubgraph
          ((G.induce (↑(rootDeletedComponentCarrier G r C) : Set V)) \
            q.toSubgraph.spanningCoe) sdiff_le).IsPerfectMatching := by
  classical
  let := Fintype.ofFinite ((G.induce {v : V | v ≠ r}).ConnectedComponent)
  have hx := hinside x p.start_mem_support
  have hy := hinside y p.end_mem_support
  have hcard := (M.rootDeleted_two_components_exact_balanced r C D hCD).2.2.1
  have hports := rootDeletedComponent_twoPort_attachment_exact r C hcard
  obtain ⟨a, b, ha, hb, hab, hra, hrb, hexact⟩ := hports
  have hroot : ∀ v, v ∈ rootDeletedComponentCarrier G r C →
      (G.Adj v r ↔ v = x ∨ v = y) := by
    intro v hv
    constructor
    · intro hvr
      have hvab := hexact v hv hvr
      have hxab := hexact x hx hrx.symm
      have hyab := hexact y hy hry.symm
      rcases hvab with rfl | rfl <;>
        rcases hxab with hxa | hxb <;> rcases hyab with hya | hyb <;>
        first | exact Or.inl hxa.symm | exact Or.inr hya.symm |
          exact Or.inl hxb.symm | exact Or.inr hyb.symm |
          exact (hxy (hxa.trans hya.symm)).elim |
          exact (hxy (hxb.trans hyb.symm)).elim
    · rintro (rfl | rfl)
      · exact hrx.symm
      · exact hry.symm
  have hboundary : ∀ v, v ∈ rootDeletedComponentCarrier G r C →
      ∀ w, w ∉ rootDeletedComponentCarrier G r C → G.Adj v w → w = r := by
    intro v hv w hw hvw
    exact ((rootDeletedComponent_boundary r M.isConnected C).1 v hv w hvw).resolve_left hw
  exact exact_two_port_spanning_path_matching
    (rootDeletedComponentCarrier G r C) r x y
    (rootDeletedComponentCarrier_nonempty_not_mem G r C).2 hx hy hxy
    hboundary hroot hcubic p hp hinside hspan

end Erdos64
