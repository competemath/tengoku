import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisAction_isUnramifiedAt_pi.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisAction_isUnramifiedAt_pi

set_option autoImplicit false

open scoped TensorProduct

/--
@isnad1 id=eq.4h8v.s12.ce23cfe4b583 from=translated src=- shape=5821504d vocab=66e0749d
-/
theorem solution
    (A : Type) [CommRing A] (ι : Type)
    (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
    (ρ : ∀ i, (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A (V i))
    (ρpi : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A (∀ i, V i))
    (hρpi : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ∀ i, V i) (i : ι),
      ρpi σ f i = ρ i σ (f i))
    (ℓ : ℕ)
    (hρ : ∀ i, ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ i σ = 1) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρpi σ = 1 := by
  intro P hP σ hσ
  refine LinearMap.ext fun f => funext fun i => ?_
  rw [hρpi, hρ i P hP σ hσ, Module.End.one_apply, Module.End.one_apply]
