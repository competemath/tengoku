import Tengoku.Erdos64.Erdos64.BridgeStrictClosedSide
import Tengoku.Erdos64.Erdos64.StrictRootedDoubleClosedSide

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A bridge is impossible in a vertex-minimal counterexample. Doubling the
smaller endpoint component at its deficient endpoint repairs minimum degree,
preserves simple-cycle lengths, and has strictly smaller order.
@isnad1 id=not.2h4v.s5.c3c7fcee9ace from=translated src=- shape=a47d6446 vocab=fc593b39
-/
theorem MinimalCounterexample.not_isBridge
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    {x z : V} (hxz : G.Adj x z) :
    ¬G.IsBridge s(x, z) := by
  classical
  intro hbridge
  obtain ⟨S, r, hclosed, hroot, hsize⟩ :=
    exists_strict_closed_side_of_bridge M.isConnected
      M.isCounterexample.1 hxz hbridge
  exact M.not_exists_strictly_smaller
    (strict_double_of_closed_side M.isCounterexample S r
      hclosed hroot hsize)

/-- If every edge leaving a carrier ends at `x`, and `z` is its only
possible neighbor of `x`, deleting `xz` separates the carrier from `x`.
@isnad1 id=isbridge.4h5v.s6.867fb1e7696a from=translated src=- shape=610cd877 vocab=82e4fe8e
-/
theorem isBridge_of_onePort_unique_neighbor
    {V : Type u} {G : SimpleGraph V}
    (K : Finset V) (x z : V)
    (hx : x ∉ K) (hz : z ∈ K)
    (hboundary :
      ∀ u, u ∈ K → ∀ v, v ∉ K → G.Adj u v → v = x)
    (hunique : ∀ u, u ∈ K → G.Adj x u → u = z) :
    G.IsBridge s(x, z) := by
  classical
  let H := G.deleteEdges {s(x, z)}
  have hclosed : ∀ a, a ∈ K → ∀ b, H.Adj a b → b ∈ K := by
    intro a ha b hab
    by_contra hb
    have habG : G.Adj a b := (SimpleGraph.deleteEdges_adj.mp hab).1
    have hbx : b = x := hboundary a ha b hb habG
    have hax : G.Adj a x := hbx ▸ habG
    have haz : a = z := hunique a ha hax.symm
    have hdeleted : ¬H.Adj x z := by
      simp [H, SimpleGraph.deleteEdges_adj]
    apply hdeleted
    simpa only [haz, hbx] using hab.symm
  have hwalk :
      ∀ {a b : V} (p : H.Walk a b), a ∈ K → b ∈ K := by
    intro a b p
    induction p with
    | nil => exact fun ha => ha
    | @cons a b c hab q ih =>
        exact fun ha => ih (hclosed a ha b hab)
  apply SimpleGraph.isBridge_iff.mpr
  intro hreach
  obtain ⟨p⟩ := hreach.symm
  exact hx (hwalk p hz)

/-- A one-port carrier in a minimal counterexample cannot have just one
attachment edge. This produces a second actual neighbor, not a repair
certificate assumed as a premise.
@isnad1 id=ex.5h5v.s7.974a2a1189b1 from=translated src=- shape=586d121e vocab=78a9449f
-/
theorem MinimalCounterexample.exists_second_onePort_neighbor
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (K : Finset V) (x z : V)
    (hx : x ∉ K) (hz : z ∈ K) (hxz : G.Adj x z)
    (hboundary :
      ∀ u, u ∈ K → ∀ v, v ∉ K → G.Adj u v → v = x) :
    ∃ w, w ∈ K ∧ G.Adj x w ∧ w ≠ z := by
  classical
  by_contra hnone
  apply M.not_isBridge hxz
  apply isBridge_of_onePort_unique_neighbor K x z hx hz hboundary
  intro w hw hxw
  by_contra hwz
  exact hnone ⟨w, hw, hxw, hwz⟩

end Erdos64
