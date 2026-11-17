import Tengoku.Seed.Analysis.Analytic.Uniqueness
import Tengoku.Seed.Analysis.Normed.Group.Quotient
import Tengoku.Seed.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Diagonal coefficients in a closed subspace

If an analytic map takes values near `x` in a closed subspace `W`, then the
diagonal values `p n (fun _ => y)` of its power series at `x` lie in `W`. This is
the first step of coefficient descent (Theorem 3.1).
-/

noncomputable section

open Filter
open scoped Topology

namespace AlternatingAnalytic

variable {K E Z : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup Z] [NormedSpace K Z]

/-- If `f` locally takes values in a closed subspace `W`, the diagonals of its power
series lie in `W`.
@isnad1 id=mem.3h9v.s9.cfa740b6a2f7 from=translated src=- shape=2b7311d3 vocab=83958d67
-/
theorem HasFPowerSeriesAt.diagonal_mem_closedSubspace
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    {p : FormalMultilinearSeries K E Z} {f : E → Z} {x : E}
    (hf : HasFPowerSeriesAt f p x) (hmem : ∀ᶠ y in 𝓝 x, f y ∈ W)
    (n : ℕ) (y : E) : p n (fun _ => y) ∈ W := by
  let : IsClosed (W : Set Z) := hW
  have hq : HasFPowerSeriesAt (W.mkQL ∘ f) (W.mkQL.compFormalMultilinearSeries p) x := by
    obtain ⟨r, hr⟩ := hf
    exact ⟨r, W.mkQL.comp_hasFPowerSeriesOnBall hr⟩
  have hz : W.mkQL ∘ f =ᶠ[𝓝 x] 0 := by
    filter_upwards [hmem] with z hz
    simpa using (Submodule.Quotient.mk_eq_zero W).mpr hz
  have hcoeff := (hq.congr hz).apply_eq_zero n y
  exact (Submodule.Quotient.mk_eq_zero W).mp hcoeff

end AlternatingAnalytic
