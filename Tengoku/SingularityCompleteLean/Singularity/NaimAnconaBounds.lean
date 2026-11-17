import Tengoku.SingularityCompleteLean.Singularity.CocompactExcessAncona
import Tengoku.SingularityCompleteLean.Singularity.NaimSubsequence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive finite bounds on off-diagonal Naïm quotients

The lower bound is universal. In the cocompact setting a fixed positive disk
separation gives the upper bound via the proved Ancona inequality. Thus any
off-diagonal disk approach has a positive finite subsequential limit. This does
not assert uniqueness or existence of the full boundary kernel.
-/

noncomputable section
open Filter
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Distinct disk limits give a positive uniform separation eventually.-/
theorem eventually_cayley_separated {α : Type*} {l : Filter α} (x y : α → ℍ)
    (a b : ℂ) (hab : a ≠ b)
    (hx : Tendsto (fun n => halfPlaneCayley (x n)) l (𝓝 a))
    (hy : Tendsto (fun n => halfPlaneCayley (y n)) l (𝓝 b)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in l, δ ≤ dist (halfPlaneCayley (x n)) (halfPlaneCayley (y n)) := by
  have hd : 0 < dist a b := dist_pos.mpr hab
  refine ⟨dist a b / 2, by positivity, ?_⟩
  exact ((hx.dist hy).eventually (lt_mem_nhds (by linarith : dist a b / 2 < dist a b))).mono
    (fun _ h => h.le)

end Singularity
