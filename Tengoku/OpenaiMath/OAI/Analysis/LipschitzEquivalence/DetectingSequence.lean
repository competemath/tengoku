import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.SelectionStep

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

structure ConstructionPrefix (K Q : Set H) (C ρ α : ℝ) (μ : ℕ → Space H)
    (ε η : ℕ → ℝ) (n : ℕ) where
  z : ℕ → Smooth H
  w : ℕ → Smooth H
  a : ℕ → RowItem K C ρ μ
  lip : ∀ i < n, LipschitzWith 1 (z i).val
  zero : ∀ i < n, (z i).val 0 = 0 ∧ (w i).val 0 = 0
  high : ∀ i < n, α ≤ smoothPair (a i).a (z i)
  mass : ∀ i j, j < i → i < n → gradMass (a i).a (z j) ≤ η j
  error : ∀ i < n, ∀ x ∈ Q,
    ‖Smooth.grad x (w i)-damping (Finset.range i) z x • Smooth.grad x (z i)‖ ≤ ε i
  rich : ((triangularRows K C ρ α μ).restrict
    (fun b => ∀ i < n, gradMass b.a (z i) ≤ η i)).Rich

namespace ConstructionPrefix
variable {K Q : Set H} {C ρ α : ℝ} {μ : ℕ → Space H} {ε η : ℕ → ℝ}

end ConstructionPrefix

end LipschitzCounterexample.CompactWSC
end

end OAI
