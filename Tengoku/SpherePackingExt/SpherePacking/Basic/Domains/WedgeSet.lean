module
public import Tengoku.Seed.Data.Complex.Basic
public import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Basic
public import Tengoku.Seed.Analysis.Convex.Basic
public import Tengoku.Seed.LinearAlgebra.AffineSpace.AffineMap
public import Tengoku.Seed.Topology.Path
import Tengoku.Seed.Tactic.Abel
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A wedge domain for contour deformation

This file defines `wedgeSet : Set ℂ`, an open convex wedge in the upper half-plane.
Its closure meets the real axis only at `1`.
This domain is used throughout the contour deformation arguments.

We also record basic topological/convexity properties, convenient closure bounds,
and membership lemmas for the line segments used in the constructions.
-/

namespace SpherePacking

noncomputable section

open Complex

/-! ## Main definition -/

/--
The wedge region used for the contour deformation.

Its closure meets the real axis only at `1`.-/
public def wedgeSet : Set ℂ :=
  {z : ℂ | 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im}

private lemma closure_wedgeSet_subset_im_nonneg :
    closure wedgeSet ⊆ {z : ℂ | 0 ≤ z.im} :=
  closure_minimal (fun _ hz => le_of_lt hz.1) (isClosed_le continuous_const continuous_im)

/-- A point in `closure wedgeSet` satisfies `|z.re - 1| ≤ z.im`.-/
public lemma closure_wedgeSet_subset_abs_re_sub_one_le_im :
    closure wedgeSet ⊆ {z : ℂ | |z.re - 1| ≤ z.im} := by
  refine closure_minimal (fun z hz => ?_)
    (isClosed_le (continuous_abs.comp (continuous_re.sub continuous_const)) continuous_im)
  exact abs_le.2 ⟨by linarith [hz.2.2], le_of_lt hz.2.1⟩

/-- If `z ∈ closure wedgeSet` and `z ≠ 1`, then `z` lies in the open upper half-plane.-/
public lemma mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one
    {z : ℂ} (hz : z ∈ closure wedgeSet) (hne : z ≠ (1 : ℂ)) :
    z ∈ UpperHalfPlane.upperHalfPlaneSet := by
  have hzIm_pos : 0 < z.im := by
    refine lt_of_le_of_ne (closure_wedgeSet_subset_im_nonneg hz) ?_
    intro hzIm
    apply hne
    have hre : z.re = 1 := by
      have habs0 : |z.re - 1| = 0 :=
        le_antisymm (by simpa [hzIm] using closure_wedgeSet_subset_abs_re_sub_one_le_im hz)
          (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp habs0)
    exact Complex.ext (by simp [hre]) (by simp [hzIm])
  simpa [UpperHalfPlane.upperHalfPlaneSet] using hzIm_pos

end

end SpherePacking
