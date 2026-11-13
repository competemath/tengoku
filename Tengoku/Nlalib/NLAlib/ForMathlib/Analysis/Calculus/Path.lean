import Tengoku.Seed.Analysis.Convex.PathConnected
import Tengoku.Seed.Analysis.Calculus.ContDiff.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Smoothness of native straight paths

Within its closed parameter interval a clamped native segment agrees
with the actual affine parametrization. Reused from the deferred contour
archive; no ambient differentiability at the clamping points is claimed.
-/

noncomputable section
open Set
open scoped unitInterval
namespace Path

/-- A straight native path is smooth within its actual parameter interval.
@isnad1 id=contdiff.0h4v.s6.0c091bd0c333 from=translated src=- shape=0c40d8ee vocab=ec0f5cf8
-/
theorem contDiffOn_extend_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) (n : WithTop ℕ∞) : ContDiffOn ℝ n (Path.segment a b).extend I := by
  have h : ContDiff ℝ n (AffineMap.lineMap a b : ℝ → E) := by
    have he : (AffineMap.lineMap a b : ℝ → E) = fun t => (1 - t) • a + t • b := by
      funext t
      simp only [AffineMap.lineMap_apply_module]
    rw [he]
    fun_prop
  exact h.contDiffOn.congr (fun t ht => eqOn_extend_segment a b ht)

end Path
