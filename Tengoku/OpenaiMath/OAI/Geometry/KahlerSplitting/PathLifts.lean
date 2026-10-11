import Tengoku.OpenaiMath.OAI.Geometry.KahlerSplitting.ProductLocal

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z}

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}
    {A : Type*} [TopologicalSpace A]

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
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
namespace UniversalCoverSplitting
lemma simplyConnected_product {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [SimplyConnectedSpace A] [SimplyConnectedSpace B] : SimplyConnectedSpace (A × B) := by
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨inferInstance,?_⟩
  intro x y p₁ p₂
  obtain ⟨H₁⟩ := SimplyConnectedSpace.paths_homotopic (p₁.map continuous_fst) (p₂.map continuous_fst)
  obtain ⟨H₂⟩ := SimplyConnectedSpace.paths_homotopic (p₁.map continuous_snd) (p₂.map continuous_snd)
  refine ⟨{ toFun := fun z ↦ (H₁ z,H₂ z)
            continuous_toFun := H₁.continuous.prodMk H₂.continuous
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    exact Prod.ext (H₁.map_zero_left t) (H₂.map_zero_left t)
  · intro t
    exact Prod.ext (H₁.map_one_left t) (H₂.map_one_left t)
  · intro t u hu
    exact Prod.ext (H₁.eq_fst t hu) (H₂.eq_fst t hu)
end UniversalCoverSplitting
end
end

end OAI
