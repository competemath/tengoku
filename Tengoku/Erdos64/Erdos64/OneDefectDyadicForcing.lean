import Tengoku.Erdos64.Erdos64.RootedDoubleNonroot
import Tengoku.Erdos64.Erdos64.RootedDoubleCycleLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A graph with just one possible degree-two defect must already contain a
dyadic cycle if its rooted double is smaller than a minimal counterexample.
The double repairs the defect without introducing any new cycle lengths.
@isnad1 id=haspower.4h5v.s7.3bb94da24a07 from=translated src=- shape=41bec4ec vocab=b1452927
-/
theorem MinimalCounterexample.one_defect_small_has_dyadic_cycle
    {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (M : MinimalCounterexample G) (y : W)
    (hy : 2 ≤ H.degree y)
    (hother : ∀ w, w ≠ y → 3 ≤ H.degree w)
    (hsize : 2 * Fintype.card W - 1 < Fintype.card V) :
    HasPowerOfTwoCycle H := by
  classical
  by_contra hno
  let K := rootedDoubleGraph H y
  let : Nonempty (RootedDoubleVertex W y) := ⟨none⟩
  have hmin : 3 ≤ K.minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree (G := K) 3
    intro z
    cases z with
    | none =>
        change 3 ≤ (rootedDoubleGraph H y).degree none
        rw [rootedDouble_root_degree_doubling]
        omega
    | some z =>
        rcases z with ⟨b, w⟩
        change 3 ≤ (rootedDoubleGraph H y).degree (some (b, w))
        rw [rootedDouble_nonroot_degree_preservation]
        exact hother w.1 w.2
  have hKno : ¬HasPowerOfTwoCycle K := by
    rintro ⟨k, z, c, hk, hc, hlen⟩
    obtain ⟨hc', hlen'⟩ := rootedDouble_cycle_localization_projection c hc
    exact hno ⟨k, rootedDoubleProjectionHom z,
      c.map rootedDoubleProjectionHom, hk, hc', hlen'.trans hlen⟩
  apply M.not_exists_strictly_smaller (H := K)
  refine ⟨⟨hmin, hKno⟩, ?_⟩
  rw [rootedDouble_card]
  exact hsize

end Erdos64
