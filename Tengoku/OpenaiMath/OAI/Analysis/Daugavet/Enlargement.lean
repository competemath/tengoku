import Tengoku.OpenaiMath.OAI.Analysis.Daugavet.Joining

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExactModuli.KW

structure EnlargementData {κ : Type} [Fintype κ] (G : Submodule ℝ KWL1)
    (u : κ → KWL1) (h : ℝ) where
  space : Submodule ℝ KWL1
  contains : G ≤ space
  finiteDimensional : FiniteDimensional ℝ space
  finiteCoordinates : FiniteCoordinates space
  copies : ℕ
  copies_pos : 0 < copies
  vectors : κ → Fin copies → KWL1
  vectors_mem : ∀ k j, vectors k j ∈ space
  vectors_unit : ∀ k j, ‖vectors k j‖ = 1
  additive : ∀ w ∈ G, ‖w‖ = 1 → ∀ k j, 2 - h ≤ ‖w + vectors k j‖
  averages : ∀ k, ‖u k - (copies : ℝ)⁻¹ • ∑ j, vectors k j‖ ≤ h
  wholeBall : ∀ g ∈ space, ‖g‖ ≤ 1 →
    ∃ ψ ∈ G, ‖ψ‖ ≤ 1 ∧ measureDistance kwMeasure g ψ ≤ h

end ExactModuli.KW

end

end OAI
