import Tengoku.SingularityCompleteLean.Singularity.CompactBoundary
import Tengoku.SingularityCompleteLean.Singularity.PeriodicStrip
import Tengoku.SingularityCompleteLean.Singularity.InfiniteWalkProcess
import Tengoku.Seed.Topology.Sequences

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Escaping orbit limits lie on the geometric boundary

A discrete subgroup has only finitely many group vertices over each compact
subset of the upper half-plane. Thus a path escaping finite sets cannot converge
to an interior point. Any limit in the compact sphere must lie on ℝ ∪ {∞}.
This does not prove that a limit exists.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- An escaping discrete-group orbit cannot have an interior limit in the compact sphere.-/
theorem escaping_orbit_limit_in_boundary (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (z : ℍ) (y : ℕ → Γ)
    (hescape : ∀ K : Finset Γ, ∀ᶠ n in atTop, y n ∉ K)
    (p : OnePoint ℂ)
    (hlim : Tendsto (fun n => hyperbolicCompactEmbedding (y n • z)) atTop (nhds p)) :
    p ∈ compactHyperbolicBoundary := by
  cases p with
  | infty => exact compactHyperbolicBoundary_infty
  | coe w =>
    rw [compactHyperbolicBoundary_coe]
    have hc : Tendsto (fun n => ((y n • z : ℍ) : ℂ)) atTop (nhds w) :=
      OnePoint.isOpenEmbedding_coe.isEmbedding.tendsto_nhds_iff.mpr hlim
    have hn : 0 ≤ w.im := ge_of_tendsto (Complex.continuous_im.tendsto w |>.comp hc)
      (Eventually.of_forall (fun n => (y n • z).im_pos.le))
    by_contra hw
    have hp : 0 < w.im := lt_of_le_of_ne hn (Ne.symm hw)
    let u : ℍ := ⟨w, hp⟩
    have ht : Tendsto (fun n => y n • z) atTop (nhds u) :=
      UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff.mpr hc
    have hK := finite_group_vertices_in_compact Γ z (isCompact_closedBall u 1)
    have hv : ∀ᶠ n in atTop, y n ∈ hK.toFinset := by
      filter_upwards [ht.eventually (Metric.closedBall_mem_nhds u zero_lt_one)] with n hn
      exact hK.mem_toFinset.mpr hn
    obtain ⟨n, hn, hne⟩ := (hv.and (hescape hK.toFinset)).exists
    exact hne hn

/-- Compactness supplies a boundary accumulation point for every escaping discrete orbit.-/
theorem escaping_orbit_boundary_subsequence (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (z : ℍ) (y : ℕ → Γ)
    (hescape : ∀ K : Finset Γ, ∀ᶠ n in atTop, y n ∉ K) :
    ∃ p ∈ compactHyperbolicBoundary, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => hyperbolicCompactEmbedding (y (φ n) • z)) atTop (nhds p) := by
  obtain ⟨p, _, φ, hφ, ht⟩ := (isCompact_univ (X := OnePoint ℂ)).tendsto_subseq
    (fun n => mem_univ (hyperbolicCompactEmbedding (y n • z)))
  refine ⟨p, escaping_orbit_limit_in_boundary Γ z (y ∘ φ) ?_ p ht, φ, hφ, ht⟩
  intro K
  exact hφ.tendsto_atTop.eventually (hescape K)

end Singularity
