import Tengoku.Seed.Combinatorics.SimpleGraph.Coloring.Constructions
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_odd_loop` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_odd_loop_at` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms component_exists_odd_loop_at` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms indexed_of_odd_loop` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms component_odd_walk` (it only prints; the queue checks the axioms of every declaration). -/

/-!
A non-two-colorable connected graph has an odd closed walk based at any
specified vertex. The same conclusion holds at a vertex whose own connected
component is non-two-colorable. The final interface indexes the actual walk by
`Fin (m + 1)`, including both endpoints, for use with finite scan arguments.
No finiteness assumption on the ambient graph is needed.
-/
namespace DeletionCode.OddGraphWalk

variable {V : Type*} {G : SimpleGraph V}

/-- Negating mathlib's closed-walk characterization of two-colorability gives
an odd loop, initially without any constraint on its base vertex.
@isnad1 id=ex.1h2v.s5.9ac4edd862a2 from=translated src=- shape=668909a7 vocab=79a8b5e1
-/
theorem exists_odd_loop (hnot : ¬ G.Colorable 2) :
    ∃ u : V, ∃ q : G.Walk u u, Odd q.length := by
  classical
  by_contra hnone
  apply hnot
  apply SimpleGraph.two_colorable_iff_forall_loop_even.mpr
  intro u q
  exact Nat.not_odd_iff_even.mp (fun hq => hnone ⟨u, q, hq⟩)

/-- Travelling to an odd loop and returning along the reverse connecting walk
changes its length by an even number.
@isnad1 id=ex.2h3v.s5.622e18b69ffe from=translated src=- shape=c4ecf4eb vocab=ef730d11
-/
theorem exists_odd_loop_at (hconnected : G.Connected)
    (hnot : ¬ G.Colorable 2) (x : V) :
    ∃ q : G.Walk x x, Odd q.length := by
  classical
  obtain ⟨u, q, hq⟩ := exists_odd_loop hnot
  let a : G.Walk x u := (hconnected x u).some
  refine ⟨(a.append q).append a.reverse, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  obtain ⟨r, hr⟩ := hq
  refine ⟨a.length + r, ?_⟩
  omega

/-- The odd loop can be based at the actual ambient vertex `x`, when only its
own induced connected component is known to be non-two-colorable.
@isnad1 id=ex.1h3v.s6.b75d001762b1 from=translated src=- shape=1286892d vocab=79a31956
-/
theorem component_exists_odd_loop_at (x : V)
    (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ q : G.Walk x x, Odd q.length := by
  classical
  let C := G.connectedComponentMk x
  let xc : C := ⟨x, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  obtain ⟨q, hq⟩ := exists_odd_loop_at C.connected_toSimpleGraph hnot xc
  have hm : Odd (q.map C.toSimpleGraph_hom).length := by
    simpa only [SimpleGraph.Walk.length_map] using hq
  exact ⟨q.map C.toSimpleGraph_hom, hm⟩

/-- A walk supplies its own finite vertex sequence: no enumeration or edge
realization assumption is added when converting to the scan interface.
@isnad1 id=ex.1h4v.s7.b831a71f12a8 from=translated src=- shape=47851a26 vocab=e664b67b
-/
theorem indexed_of_odd_loop {x : V} (q : G.Walk x x) (hq : Odd q.length) :
    ∃ m : ℕ, Odd m ∧ ∃ vertices : Fin (m + 1) → V,
      vertices 0 = x ∧ vertices (Fin.last m) = x ∧
        ∀ i : Fin m, G.Adj (vertices i.castSucc) (vertices i.succ) := by
  refine ⟨q.length, hq, fun i => q.getVert i.val, ?_, ?_, ?_⟩
  · exact q.getVert_zero
  · exact q.getVert_length
  · intro i
    exact q.adj_getVert_succ i.isLt

/-- Finite-index form for a non-two-colorable connected graph.
@isnad1 id=ex.2h3v.s6.a5e8e690ca72 from=translated src=- shape=35b3cd99 vocab=846297cf
-/
theorem connected_odd_walk (hconnected : G.Connected)
    (hnot : ¬ G.Colorable 2) (x : V) :
    ∃ m : ℕ, Odd m ∧ ∃ vertices : Fin (m + 1) → V,
      vertices 0 = x ∧ vertices (Fin.last m) = x ∧
        ∀ i : Fin m, G.Adj (vertices i.castSucc) (vertices i.succ) := by
  obtain ⟨q, hq⟩ := exists_odd_loop_at hconnected hnot x
  exact indexed_of_odd_loop q hq

/-- Finite-index form based at `x`, assuming only that the component containing
`x` is non-two-colorable. Other components impose no hypotheses.
@isnad1 id=ex.1h3v.s7.94ba74fba575 from=translated src=- shape=1e23df02 vocab=f70148d1
-/
theorem component_odd_walk (x : V)
    (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ m : ℕ, Odd m ∧ ∃ vertices : Fin (m + 1) → V,
      vertices 0 = x ∧ vertices (Fin.last m) = x ∧
        ∀ i : Fin m, G.Adj (vertices i.castSucc) (vertices i.succ) := by
  obtain ⟨q, hq⟩ := component_exists_odd_loop_at x hnot
  exact indexed_of_odd_loop q hq

end DeletionCode.OddGraphWalk
