import Tengoku.SingularityCompleteLean.Singularity.GeometricMartinContinuity
import Tengoku.SingularityCompleteLean.Singularity.MartinAction
import Tengoku.SingularityCompleteLean.Singularity.PoissonMobius

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Covariance of the constructed geometric Martin map

The finite real-chart map intertwines the actual Martin-boundary action with
the Möbius action wherever the transformed endpoint is finite. The kernel
formula follows from the exact action on finite Green quotients and the now
proved convergence along arbitrary approaches.
-/

noncomputable section
open Filter Set
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Möbius transformations preserve finite-boundary convergence away from their
pole. The denominator condition says precisely that the image is finite.
@isnad1 id=tendsto.2h5v.s8.070ce7c5fd78 from=translated src=- shape=72508667 vocab=500087e7
-/
theorem real_boundary_smul_tendsto {α : Type*} {l : Filter α}
    (g : SL(2, ℝ)) (ξ : ℝ) (hg : g 1 0 * ξ + g 1 1 ≠ 0)
    (z : α → ℍ) (hz : Tendsto (fun n => (z n : ℂ)) l (𝓝 (ξ : ℂ))) :
    Tendsto (fun n => ((g • z n : ℍ) : ℂ)) l (𝓝 (realBoundaryMobius g ξ : ℂ)) := by
  have hd : (g 1 0 : ℂ) * (ξ : ℂ) + (g 1 1 : ℂ) ≠ 0 := by exact_mod_cast hg
  have hh := ((hz.const_mul (g 0 0 : ℂ)).add_const (g 0 1 : ℂ)).div
    ((hz.const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ)) hd
  change Tendsto (fun n => ((g 0 0 : ℂ) * (z n : ℂ) + (g 0 1 : ℂ)) /
    ((g 1 0 : ℂ) * (z n : ℂ) + (g 1 1 : ℂ))) l
    (𝓝 (((g 0 0 : ℂ) * (ξ : ℂ) + (g 0 1 : ℂ)) /
      ((g 1 0 : ℂ) * (ξ : ℂ) + (g 1 1 : ℂ)))) at hh
  simpa only [UpperHalfPlane.coe_specialLinearGroup_apply, realBoundaryMobius,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul,
    RingHom.id_apply, Algebra.algebraMap_self] using hh

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

end Singularity
