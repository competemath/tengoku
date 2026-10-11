import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.Main

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
namespace CompleteCrouzeix
open Set Filter Metric Complex
open scoped Topology

def LocalClosedAnalyticBoundary (U : Set ℂ) (p : ℂ) : Prop :=
  ∃ χ : ℂ → ℂ, χ 0 = p ∧ AnalyticAt ℂ χ 0 ∧ deriv χ 0 ≠ 0 ∧
    (∀ᶠ z : ℂ in 𝓝 0, χ z ∈ U ↔ 0 < z.im) ∧
    (∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → χ z ∈ frontier U) ∧
    (∀ᶠ z : ℂ in 𝓝 0, χ z ∈ closure U ↔ 0 ≤ z.im)

end CompleteCrouzeix
end

end OAI
