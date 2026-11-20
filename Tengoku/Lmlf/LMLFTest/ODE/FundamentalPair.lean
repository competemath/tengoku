import Tengoku.Lmlf.LMLF.ODE.FundamentalPair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Public-use tests for fundamental pairs
-/

open Function Set

namespace LMLFTest.ODE

/--
@isnad1 id=iff.2h8v.s5.db32069723f4 from=translated src=- shape=7748ab8c vocab=8e72baf9
-/
theorem spanning_offDomain_invariant
    {𝕂 : Type*} [RCLike 𝕂] {I : Set ℝ} {f g y₁ y₂ z₁ z₂ : ℝ → 𝕂}
    (hy₁ : EqOn y₁ z₁ I) (hy₂ : EqOn y₂ z₂ I) :
    LMLF.ODE.SpansSecondOrderLinearSolutionsOn I f g y₁ y₂ ↔
      LMLF.ODE.SpansSecondOrderLinearSolutionsOn I f g z₁ z₂ := by
  constructor
  · intro h y v hy hv
    obtain ⟨A, B, hEq⟩ := h y v hy hv
    refine ⟨A, B, hEq.trans ?_⟩
    intro x hx
    change A * y₁ x + B * y₂ x = A * z₁ x + B * z₂ x
    rw [hy₁ hx, hy₂ hx]
  · intro h y v hy hv
    obtain ⟨A, B, hEq⟩ := h y v hy hv
    refine ⟨A, B, hEq.trans ?_⟩
    intro x hx
    change A * z₁ x + B * z₂ x = A * y₁ x + B * y₂ x
    rw [← hy₁ hx, ← hy₂ hx]

/--
@isnad1 id=iff.2h7v.s8.8a2961a2c870 from=translated src=- shape=d45bb846 vocab=f81e0f0e
-/
theorem restricted_independence_offDomain_invariant
    {X K : Type*} [Ring K] {I : Set X} {y₁ y₂ z₁ z₂ : X → K}
    (hy₁ : EqOn y₁ z₁ I) (hy₂ : EqOn y₂ z₂ I) :
    LinearIndependent K ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)] ↔
      LinearIndependent K ![(fun x : I ↦ z₁ x.1), (fun x : I ↦ z₂ x.1)] := by
  rw [LMLF.ODE.linearIndependent_restrict_pair_iff,
    LMLF.ODE.linearIndependent_restrict_pair_iff]
  constructor
  · intro h A B hzero
    apply h A B
    intro x hx
    simpa [hy₁ hx, hy₂ hx] using hzero hx
  · intro h A B hzero
    apply h A B
    intro x hx
    simpa [hy₁ hx, hy₂ hx] using hzero hx

/--
@isnad1 id=ex.5h4v.s8.623d3d68694c from=translated src=- shape=c3252d30 vocab=1a1a757d
-/
theorem complexCanonicalFundamentalPair_consumer
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℂ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ∃ y₁ y₂ : ℝ → ℂ,
      ContDiffOn ℝ 2 y₁ I ∧ ContDiffOn ℝ 2 y₂ I ∧
      LMLF.ODE.SpansSecondOrderLinearSolutionsOn I f g y₁ y₂ ∧
      LinearIndependent ℂ ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)] := by
  obtain ⟨y₁, v₁, y₂, v₂, hy₁₀, hv₁₀, hy₂₀, hv₂₀,
    hy₁, hv₁, hy₂, hv₂, hy₁C2, hy₂C2, hW, hspan, hind, hrepr⟩ :=
    LMLF.ODE.exists_complexCanonicalFundamentalPair hI hIc hf hg hx₀
  exact ⟨y₁, y₂, hy₁C2, hy₂C2, hspan, hind⟩

/--
@isnad1 id=ex.5h4v.s8.a41640f6f3f6 from=translated src=- shape=d5061919 vocab=826bd50d
-/
theorem realCanonicalFundamentalPair_consumer
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℝ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ∃ y₁ y₂ : ℝ → ℝ,
      ContDiffOn ℝ 2 y₁ I ∧ ContDiffOn ℝ 2 y₂ I ∧
      LMLF.ODE.SpansSecondOrderLinearSolutionsOn I f g y₁ y₂ ∧
      LinearIndependent ℝ ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)] := by
  obtain ⟨y₁, v₁, y₂, v₂, hy₁₀, hv₁₀, hy₂₀, hv₂₀,
    hy₁, hv₁, hy₂, hv₂, hy₁C2, hy₂C2, hW, hspan, hind, hrepr⟩ :=
    LMLF.ODE.exists_realCanonicalFundamentalPair hI hIc hf hg hx₀
  exact ⟨y₁, y₂, hy₁C2, hy₂C2, hspan, hind⟩

end LMLFTest.ODE
