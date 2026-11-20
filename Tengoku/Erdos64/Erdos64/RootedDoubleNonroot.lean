import Tengoku.Erdos64.Erdos64.RootedDouble
import Tengoku.Erdos64.Erdos64.RootedDoubleNeighbors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- The neighbors of a nonroot copy vertex are exactly the original
neighbors, with an original-root neighbor represented by the shared root.-/
noncomputable def rootedDouble_nonroot_neighborEquiv
    {V : Type u} {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] {r : V} (b : Bool)
    (v : {v : V // v ≠ r}) :
    (rootedDoubleGraph G r).neighborSet (some (b, v)) ≃
      G.neighborSet v.1 where
  toFun w :=
    ⟨rootedDoubleProjection w.1, by
      simpa [SimpleGraph.mem_neighborSet, rootedDoubleGraph,
        rootedDoubleProjection, rootedDoubleCompatible] using w.2.1⟩
  invFun w :=
    if hwr : w.1 = r then
      ⟨none, by
        rw [SimpleGraph.mem_neighborSet]
        simpa [rootedDoubleGraph, rootedDoubleProjection,
          rootedDoubleCompatible, hwr] using w.2⟩
    else
      ⟨some (b, ⟨w.1, hwr⟩), by
        rw [SimpleGraph.mem_neighborSet]
        change G.Adj v.1 w.1 ∧ b = b
        exact ⟨(G.mem_neighborSet v.1 w.1).mp w.2, rfl⟩⟩
  left_inv := by
    rintro ⟨w, hw⟩
    cases w with
    | none =>
        apply Subtype.ext
        simp [rootedDoubleProjection]
    | some bw =>
        rcases bw with ⟨b', w⟩
        have hwr : w.1 ≠ r := w.2
        have hadj : (rootedDoubleGraph G r).Adj
            (some (b, v)) (some (b', w)) := by
          simpa only [SimpleGraph.mem_neighborSet] using hw
        have htag : b = b' := by
          simpa [rootedDoubleCompatible] using hadj.2
        apply Subtype.ext
        simp [rootedDoubleProjection, hwr, htag]
  right_inv := by
    rintro ⟨w, hw⟩
    by_cases hwr : w = r
    · subst w
      apply Subtype.ext
      simp [rootedDoubleProjection]
    · apply Subtype.ext
      simp [rootedDoubleProjection, hwr]

/- Every nonroot copy vertex has the degree of its original vertex. -/
/--
@isnad1 id=eq.0h5v.s7.36592d0c9f70 from=translated src=- shape=2e09a1f9 vocab=4d3954d1
-/
theorem rootedDouble_nonroot_degree_preservation
    {V : Type u} {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] {r : V}
    (b : Bool) (v : {v : V // v ≠ r}) :
    (rootedDoubleGraph G r).degree (some (b, v)) = G.degree v.1 :=
  rootedDouble_nonroot_degree_preservation_of_neighborEquiv b v
    (rootedDouble_nonroot_neighborEquiv b v)

end Erdos64
