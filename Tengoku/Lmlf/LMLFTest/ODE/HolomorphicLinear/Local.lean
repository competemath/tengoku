import Tengoku.Lmlf.LMLF.ODE.HolomorphicLinear.Local

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Metric Set

namespace LMLFTest.ODE

universe u

/-- The disk theorem retains universe-polymorphic Banach values, an arbitrary
basepoint, and its on-disk `EqOn` uniqueness conclusion.-/
theorem genericHolomorphicLinearIVP_ball
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R : ℝ} (hR : 0 < R) {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A (ball q R))
    {x₀ : ℂ} (hx₀ : x₀ ∈ ball q R) (u₀ : E) :
    ∃ u : ℂ → E, u x₀ = u₀ ∧ AnalyticOnNhd ℂ u (ball q R) ∧
      (∀ z ∈ ball q R, HasDerivAt u (A z (u z)) z) ∧
      ∀ v : ℂ → E, v x₀ = u₀ → AnalyticOnNhd ℂ v (ball q R) →
        (∀ z ∈ ball q R, HasDerivAt v (A z (v z)) z) → EqOn u v (ball q R) :=
  LMLF.ODE.exists_unique_holomorphicLinearIVP_ball hR hA hx₀ u₀

/-- For the zero coefficient, the public uniqueness clause identifies the
constructed solution with the constant function.-/
theorem zeroCoefficient_holomorphicLinearIVP
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q x₀ : ℂ} {R : ℝ} (hR : 0 < R) (hx₀ : x₀ ∈ ball q R) (u₀ : E) :
    ∃ u : ℂ → E, u x₀ = u₀ ∧ AnalyticOnNhd ℂ u (ball q R) ∧
      (∀ z ∈ ball q R, HasDerivAt u 0 z) ∧ EqOn u (fun _ ↦ u₀) (ball q R) := by
  obtain ⟨u, hu₀, huAnalytic, huOde, huUnique⟩ :=
    LMLF.ODE.exists_unique_holomorphicLinearIVP_ball hR
      (A := fun _ ↦ 0) analyticOnNhd_const hx₀ u₀
  refine ⟨u, hu₀, huAnalytic, ?_, ?_⟩
  · intro z hz
    simpa using huOde z hz
  · apply huUnique (fun _ ↦ u₀) rfl analyticOnNhd_const
    intro z hz
    exact hasDerivAt_const z u₀

end LMLFTest.ODE
