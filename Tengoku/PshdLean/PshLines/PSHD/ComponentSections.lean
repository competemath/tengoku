import Tengoku.PshdLean.PshLines.Plurisubharmonic
import Tengoku.Seed.Analysis.Normed.Module.Connected

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Subharmonicity on connected components

On an open set, the disc criterion can be checked on its connected
components. This implements the component convention for planar sections
in Lemma 1.2 of `pshd-vibe`.
-/

open Set Filter Metric
open scoped Topology

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every affine closed complex disc is preconnected.-/
theorem isPreconnected_affineClosedDisc (x v : E) (r : ℝ) :
    IsPreconnected (affineClosedDisc x v r) := by
  apply (isPreconnected_closedBall (x := (0 : ℂ)) (r := r)).image
  fun_prop

/-- A disc in a set lies in the connected component containing its center.-/
theorem affineClosedDisc_subset_connectedComponentIn {U : Set E}
    {x v : E} {r : ℝ} (hr : 0 ≤ r) (hD : affineClosedDisc x v r ⊆ U) :
    affineClosedDisc x v r ⊆ connectedComponentIn U x :=
  (isPreconnected_affineClosedDisc x v r).subset_connectedComponentIn
    (center_mem_affineClosedDisc x v hr) hD

/-- The disc criterion on each connected component of an open set implies
the disc criterion on the whole open set.-/
theorem discPshOn_of_connectedComponentIn [LocallyConnectedSpace E]
    {u : E → EReal} {U : Set E} (hU : IsOpen U)
    (hu : ∀ x ∈ U, DiscPshOn u (connectedComponentIn U x)) : DiscPshOn u U := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (hu x hx).ne_top x (mem_connectedComponentIn hx)
  · intro x hx
    have hux := (hu x hx).upperSemicontinuousOn x (mem_connectedComponentIn hx)
    have hat : UpperSemicontinuousAt u x := by
      simpa only [UpperSemicontinuousWithinAt, UpperSemicontinuousAt,
        SemicontinuousWithinAt, SemicontinuousAt,
        nhdsWithin_eq_nhds.mpr (hU.connectedComponentIn.mem_nhds
          (mem_connectedComponentIn hx))] using hux
    exact hat.upperSemicontinuousWithinAt U
  · intro x v r hr hD C hC
    exact (hu x (hD (center_mem_affineClosedDisc x v hr.le))).submean x v r hr
      (affineClosedDisc_subset_connectedComponentIn hr.le hD) C hC

end PshLines.PSHD
