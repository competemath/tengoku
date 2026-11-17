import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_charpoly_eq_of_isEquiv.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_charpoly_eq_of_isEquiv

theorem solution {A : Type} [CommRing A] [IsLocalRing A] {ρ₁ ρ₂ : GaloisRepAdic A} (h : ρ₁.IsEquiv ρ₂) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ) := by
  obtain ⟨e⟩ := h
  have hconj : ρ₂.ρ σ = (e.toLinearEquiv : ρ₁.V →ₗ[A] ρ₂.V) ∘ₗ ρ₁.ρ σ ∘ₗ
      (e.toLinearEquiv.symm : ρ₂.V →ₗ[A] ρ₁.V) := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e.map_apply,
      LinearEquiv.apply_symm_apply]
  rw [hconj]
  exact (LinearEquiv.charpoly_conj e.toLinearEquiv (ρ₁.ρ σ)).symm
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
