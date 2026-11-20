import Tengoku.Lmlf.LMLF.ODE.LinearSecondOrder
import Tengoku.Lmlf.LMLF.ODE.Wronskian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cross-module tests for global linear IVPs

The canonical initial data produce real and complex pairs whose Wronskians
are nowhere zero on the coefficient interval.
-/

open Set

namespace LMLFTest.ODE

/-- The canonical complex IVP pair has nowhere-vanishing Wronskian.-/
theorem complexCanonicalLinearIVP_wronskian_ne_zero
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℂ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ∃ y₁ v₁ y₂ v₂ : ℝ → ℂ,
      y₁ x₀ = 1 ∧ v₁ x₀ = 0 ∧ y₂ x₀ = 0 ∧ v₂ x₀ = 1 ∧
      (∀ x ∈ I, HasDerivAt y₁ (v₁ x) x) ∧
      (∀ x ∈ I, HasDerivAt v₁ (-f x * v₁ x - g x * y₁ x) x) ∧
      (∀ x ∈ I, HasDerivAt y₂ (v₂ x) x) ∧
      (∀ x ∈ I, HasDerivAt v₂ (-f x * v₂ x - g x * y₂ x) x) ∧
      ∀ x ∈ I, LMLF.ODE.wronskian y₁ v₁ y₂ v₂ x ≠ 0 := by
  obtain ⟨y₁, v₁, hy₁₀, hv₁₀, hy₁, hv₁, hy₁C2, hu₁⟩ :=
    LMLF.ODE.exists_unique_complexLinearIVP hI hIc hf hg hx₀ 1 0
  obtain ⟨y₂, v₂, hy₂₀, hv₂₀, hy₂, hv₂, hy₂C2, hu₂⟩ :=
    LMLF.ODE.exists_unique_complexLinearIVP hI hIc hf hg hx₀ 0 1
  refine ⟨y₁, v₁, y₂, v₂, hy₁₀, hv₁₀, hy₂₀, hv₂₀,
    hy₁, hv₁, hy₂, hv₂, ?_⟩
  intro x hx hzero
  have hbase := (LMLF.ODE.wronskian_eq_zero_iff hI hIc hf hy₁ hv₁ hy₂ hv₂ hx₀ hx).1 hzero
  simp [LMLF.ODE.wronskian, hy₁₀, hv₁₀, hy₂₀, hv₂₀] at hbase

/-- The canonical real IVP pair has nowhere-vanishing Wronskian.-/
theorem realCanonicalLinearIVP_wronskian_ne_zero
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℝ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ∃ y₁ v₁ y₂ v₂ : ℝ → ℝ,
      y₁ x₀ = 1 ∧ v₁ x₀ = 0 ∧ y₂ x₀ = 0 ∧ v₂ x₀ = 1 ∧
      (∀ x ∈ I, HasDerivAt y₁ (v₁ x) x) ∧
      (∀ x ∈ I, HasDerivAt v₁ (-f x * v₁ x - g x * y₁ x) x) ∧
      (∀ x ∈ I, HasDerivAt y₂ (v₂ x) x) ∧
      (∀ x ∈ I, HasDerivAt v₂ (-f x * v₂ x - g x * y₂ x) x) ∧
      ∀ x ∈ I, LMLF.ODE.realWronskian y₁ v₁ y₂ v₂ x ≠ 0 := by
  obtain ⟨y₁, v₁, hy₁₀, hv₁₀, hy₁, hv₁, hy₁C2, hu₁⟩ :=
    LMLF.ODE.exists_unique_realLinearIVP hI hIc hf hg hx₀ 1 0
  obtain ⟨y₂, v₂, hy₂₀, hv₂₀, hy₂, hv₂, hy₂C2, hu₂⟩ :=
    LMLF.ODE.exists_unique_realLinearIVP hI hIc hf hg hx₀ 0 1
  refine ⟨y₁, v₁, y₂, v₂, hy₁₀, hv₁₀, hy₂₀, hv₂₀,
    hy₁, hv₁, hy₂, hv₂, ?_⟩
  intro x hx hzero
  have hbase :=
    (LMLF.ODE.realWronskian_eq_zero_iff hI hIc hf hy₁ hv₁ hy₂ hv₂ hx₀ hx).1 hzero
  simp [LMLF.ODE.realWronskian, LMLF.ODE.wronskian, hy₁₀, hv₁₀, hy₂₀, hv₂₀]
    at hbase

end LMLFTest.ODE
