import Tengoku.OpenaiMath.OAI.Geometry.PinnedDistances.BoundedRates

namespace OAI

universe u1 u2 u3

section
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace WeakPinned
open Bounded Global Variance Hierarchy NumberField

variable {V : ℕ → Type u1} {I : ℕ → Type u2} {K : ℕ → Type u3} [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]
variable (G : ∀ j,Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j,V j → K j) (h₁ : ∀ j,Function.Injective (Z₁ j)) (h₂ : ∀ j,Function.Injective (Z₂ j))

end WeakPinned

end
end

end OAI
