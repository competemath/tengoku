import Tengoku.OpenaiMath.OAI.RepresentationTheory.FoulkesHowe.Model
import Tengoku.OpenaiMath.OAI.RepresentationTheory.FoulkesHowe.LinearCase
import Tengoku.OpenaiMath.OAI.RepresentationTheory.FoulkesHowe.PairingConstruction
import Tengoku.OpenaiMath.OAI.RepresentationTheory.FoulkesHowe.Surjectivity
import Tengoku.OpenaiMath.OAI.RepresentationTheory.FoulkesHowe.ProductVanishing

namespace OAI

noncomputable section

universe u

namespace Problem346

theorem canonical_foulkes_howe_a_one :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : ℕ), ∃ μ : SymPow b (SymPow 1 V) →ₗ[ℂ] SymPow 1 (SymPow b V), IsFoulkesMap 1 b V μ ∧ Function.Bijective μ ∧ ∀ ν : SymPow b (SymPow 1 V) →ₗ[ℂ] SymPow 1 (SymPow b V), IsFoulkesMap 1 b V ν → ν = μ := by
  intro V _ _ _ b
  exact canonical_foulkes_howe_a_one_aux V b

end Problem346

end

end OAI
