import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A vertex-minimal counterexample whose edge count is least among all
counterexamples of the same order, including graphs on a different vertex type.

This is stronger than `EdgeMinimalCounterexample`, which only forbids proper
edge deletions from the supplied graph. It permits comparison with constructions
such as rooted doubles that preserve the vertex count but change the graph.-/
structure GlobalEdgeMinimalCounterexample
    {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] : Prop where
  vertexMinimal : MinimalCounterexample G
  edgeCountMinimal :
    ∀ (W : Type u) (H : SimpleGraph W)
      [Fintype W] [DecidableRel H.Adj],
      IsCounterexample H → Fintype.card W = Fintype.card V →
        G.edgeSet.ncard ≤ H.edgeSet.ncard

/-- Among counterexamples of minimum vertex count, minimize the edge count.
The selected graph has the same number of vertices as the input, but need not
be an edge deletion of it.-/
theorem MinimalCounterexample.exists_globalEdgeMinimalCounterexample
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (minimalCounterexample : MinimalCounterexample G) :
    ∃ (W : Type u) (H : SimpleGraph W) (_ : Fintype W)
      (_ : DecidableRel H.Adj),
      GlobalEdgeMinimalCounterexample H ∧ Fintype.card W = Fintype.card V := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (W : Type u) (H : SimpleGraph W) (_ : Fintype W)
      (_ : DecidableRel H.Adj),
      Fintype.card W = Fintype.card V ∧ IsCounterexample H ∧
        H.edgeSet.ncard = n
  have hP : ∃ n, P n := by
    exact ⟨G.edgeSet.ncard, V, G, inferInstance, inferInstance,
      rfl, minimalCounterexample.isCounterexample, rfl⟩
  obtain ⟨W, H, hW, hD, hcard, hcounter, hedges⟩ := Nat.find_spec hP
  let : Fintype W := hW
  let : DecidableRel H.Adj := hD
  refine ⟨W, H, hW, hD, ?_, hcard⟩
  refine
    { vertexMinimal :=
        { isCounterexample := hcounter
          minimal := ?_ }
      edgeCountMinimal := ?_ }
  · intro X K _ _ hK
    rw [hcard]
    exact minimalCounterexample.minimal X K hK
  · intro X K hX hKdec hK hXcard
    rw [hedges]
    apply Nat.find_min' hP
    exact ⟨X, K, hX, hKdec, hXcard.trans hcard, hK, rfl⟩

/-- Failure of the conjecture supplies a counterexample minimizing vertex
count first and edge count second. This selection does not assert that any
counterexample actually exists.-/
theorem exists_globalEdgeMinimalCounterexample
    (hnot : ¬ Conjecture.{u}) :
    ∃ (V : Type u) (G : SimpleGraph V) (_ : Fintype V)
      (_ : DecidableRel G.Adj), GlobalEdgeMinimalCounterexample G := by
  obtain ⟨V, G, hV, hD, hminimal⟩ := exists_minimalCounterexample hnot
  let : Fintype V := hV
  let : DecidableRel G.Adj := hD
  obtain ⟨W, H, hW, hH, hglobal, _⟩ :=
    hminimal.exists_globalEdgeMinimalCounterexample
  exact ⟨W, H, hW, hH, hglobal⟩

/-- Global edge-count minimality implies the existing edge-deletion minimality
interface, so structural results using that interface remain available.-/
theorem GlobalEdgeMinimalCounterexample.toEdgeMinimalCounterexample
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (minimalCounterexample : GlobalEdgeMinimalCounterexample G) :
    EdgeMinimalCounterexample G := by
  classical
  refine
    { vertexMinimal := minimalCounterexample.vertexMinimal
      edgeMinimal := ?_ }
  intro H _ hH hHG
  have hcard : G.edgeSet.ncard ≤ H.edgeSet.ncard :=
    minimalCounterexample.edgeCountMinimal V H hH rfl
  apply SimpleGraph.edgeSet_inj.mp
  exact Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_mono hHG) hcard

end Erdos64
