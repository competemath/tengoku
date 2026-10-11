import Tengoku.OpenaiMath.OAI.Geometry.KahlerSplitting.PathLifts

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
namespace UniversalCoverSplitting
namespace ProductRetracts
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}
    [CompactSpace X.Carrier] (g : KahlerMetric X) (P : ProductRetracts π o h₁ h₂)

end ProductRetracts
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z}

lemma CoverProductChart.derivative_down (e : CoverProductChart π S) {z : Z.Carrier}
    (hz : z ∈ e.chart.source) (v : Tangent Z z) :
    mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z v=
      mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.downstairs.chart (π.projection z)
        (mfderiv (model n) (model n) π.projection z v) := by
  have heq : (e.chart : Z.Carrier → _) =ᶠ[𝓝 z] e.downstairs.chart ∘ π.projection := by
    filter_upwards [e.chart.open_source.mem_nhds hz] with w hw
    exact e.coordinates w hw
  have H := mfderiv_comp (I := model n) (I' := model n) (I'' := 𝓘(ℂ,Model r × Model s)) z
    (e.downstairs.holomorphic.mdifferentiableAt (e.downstairs.chart.open_source.mem_nhds (e.maps hz)))
    (π.liftedComplexStructure.mdifferentiable z)
  have hderiv : mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z =
      mfderiv (model n) 𝓘(ℂ,Model r × Model s) (e.downstairs.chart ∘ π.projection) z :=
    heq.mfderiv_eq
  rw [←hderiv] at H
  exact congrArg (fun L : Model n →L[ℂ] (Model r × Model s) ↦ L v) H

namespace ProductRetracts
variable {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}
    [CompactSpace X.Carrier] (g : KahlerMetric X) (P : ProductRetracts π o h₁ h₂)

end ProductRetracts
end UniversalCoverSplitting
end
end

end OAI
