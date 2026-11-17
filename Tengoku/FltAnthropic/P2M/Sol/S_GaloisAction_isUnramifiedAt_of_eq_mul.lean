import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisAction_isUnramifiedAt_of_eq_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisAction_isUnramifiedAt_of_eq_mul

set_option autoImplicit false

open scoped TensorProduct

/--
@isnad1 id=eq.5h8v.s13.648d702d67d2 from=translated src=- shape=a06f54ec vocab=135045f3
-/
theorem solution
    (A : Type) [CommRing A] (V : Type) [AddCommGroup V] [Module A V]
    (ρ₁ ρ₂ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V)
    (hρ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ σ = ρ₁ σ * ρ₂ σ)
    (ℓ : ℕ)
    (h₁ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ₁ σ = 1)
    (h₂ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ₂ σ = 1) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ σ = 1 := by
  intro P hP σ hσ
  rw [hρ, h₁ P hP σ hσ, h₂ P hP σ hσ, mul_one]
