import Tengoku.Hellingerrepolean4.Hellinger.QuotientInformation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The complete linear-quotient lemma, with a single Boolean quotient
function working simultaneously for all convex tests, Hellinger objectives,
and actual mutual informations. -/

set_option autoImplicit false
noncomputable section

namespace Hellinger.QuotientContracts
open F2Model

/--
@isnad1 id=ex.2h4v.s11.ae0363cf425e from=translated src=- shape=088a2f36 vocab=8ec7f6b7
-/
theorem linear_quotient (n k : ℕ) (L : Cube n →ₗ[F2] Cube k)
    (hL : Function.Surjective L) (g : Cube k → ℝ)
    (hg : ∀ x, g x = -1 ∨ g x = 1) :
    ∃ g₀ : Cube k → ℝ, (∀ x, g₀ x = -1 ∨ g₀ x = 1) ∧
      mean g₀ = mean (g ∘ L) ∧
      (∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (Ψ : ℝ → ℝ),
        ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) Ψ →
        mean (fun y => Ψ ((noise (Fin n) ρ hρ).apply (g ∘ L) y)) ≤
          mean (fun y => Ψ ((noise (Fin k) ρ hρ).apply g₀ y))) ∧
      (∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1),
        objective ((noise (Fin n) ρ hρ).apply (g ∘ L)) ≤
          objective ((noise (Fin k) ρ hρ).apply g₀)) ∧
      (∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1),
        FiniteInformation.bscMutualInformation ((g ∘ L) ∘ bitsEquiv (Fin n)) ρ hρ ≤
          FiniteInformation.bscMutualInformation (g₀ ∘ bitsEquiv (Fin k)) ρ hρ) := by
  obtain ⟨M, hm, hc, hI⟩ := QuotientInformation.linear_quotient_information n k L hL g hg
  refine ⟨g ∘ M, (fun x => hg _), hm, hc, ?_, hI⟩
  intro ρ hρ
  have h := hc ρ hρ (fun t => -root t) root_concave.neg
  rw [mean_neg, mean_neg] at h
  simp only [objective, UniformChannel.mean_apply, hm]
  linarith

end Hellinger.QuotientContracts
